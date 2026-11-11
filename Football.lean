set_option linter.constructorNameAsVariable false

/-- Apply f, k times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0,     x => x
  | k + 1, x => iter f k (f x)

/-- Update one entry of a function (no Mathlib needed). -/
def upd (f : Nat → Nat) (i v : Nat) : Nat → Nat :=
  fun j => if j = i then v else f j

/-- Reference machine: register machine, one register per index. -/
inductive Instr
  | inc   (reg : Nat) (next : Nat)
  | jzdec (reg : Nat) (next zero : Nat)
  | halt

structure Cfg where
  pc   : Nat
  regs : Nat → Nat

def minskyStep (p : Nat → Instr) (c : Cfg) : Cfg :=
  match p c.pc with
  | .inc r n     => ⟨n, upd c.regs r (c.regs r + 1)⟩
  | .jzdec r n z => if c.regs r = 0 then ⟨z, c.regs⟩
                    else ⟨n, upd c.regs r (c.regs r - 1)⟩
  | .halt        => c

/-- Football cards played by gods. God number `i` is a player. -/
inductive Card
  | godScores (god : Nat) (next : Nat)               -- god scores a goal
  | godTackled (god : Nat) (next noGoals : Nat)      -- remove a goal, or branch if none
  | finalWhistle

/-- The Pantheon match: which card is in play, and every god's goal tally.
    The roster is indexed by Nat, so more gods can always join. -/
structure Pantheon where
  phase  : Nat
  roster : Nat → Nat

def Instr.toCard : Instr → Card
  | .inc r n     => .godScores r n
  | .jzdec r n z => .godTackled r n z
  | .halt        => .finalWhistle

def playStep (deck : Nat → Card) (m : Pantheon) : Pantheon :=
  match deck m.phase with
  | .godScores g n     => ⟨n, upd m.roster g (m.roster g + 1)⟩
  | .godTackled g n z  => if m.roster g = 0 then ⟨z, m.roster⟩
                          else ⟨n, upd m.roster g (m.roster g - 1)⟩
  | .finalWhistle      => m

def encode (c : Cfg) : Pantheon := ⟨c.pc, c.regs⟩

/-- One match = one machine step. -/
theorem pantheon_simulates (p : Nat → Instr) (c : Cfg) :
    playStep (fun i => (p i).toCard) (encode c) = encode (minskyStep p c) := by
  simp only [playStep, minskyStep, encode]
  cases h : p c.pc with
  | inc r n => simp [Instr.toCard]
  | jzdec r n z => by_cases hz : c.regs r = 0 <;> simp [Instr.toCard, hz]
  | halt => simp [Instr.toCard]

/-- A whole eternal league: k matches = k machine steps. -/
theorem eternal_league (p : Nat → Instr) (k : Nat) (c : Cfg) :
    iter (playStep (fun i => (p i).toCard)) k (encode c)
      = encode (iter (minskyStep p) k c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [iter]
    rw [pantheon_simulates, ih]

#print axioms pantheon_simulates
#print axioms eternal_league

/-! ## A real program: Zeus (god 0) gives all his goals to Athena (god 1). -/
def transfer : Nat → Instr
  | 0 => .jzdec 0 1 3   -- Zeus has a goal? take it, else go finish
  | 1 => .inc 1 2       -- Athena scores it
  | 2 => .jzdec 2 0 0   -- register 2 is always 0 -> jump back to 0
  | _ => .halt

def run (p : Nat → Instr) (c : Cfg) (k : Nat) : Cfg := iter (minskyStep p) k c

def start : Cfg := ⟨0, fun i => if i = 0 then 5 else 0⟩
def after : Cfg := run transfer start 100

#eval (after.regs 0, after.regs 1)   -- expect (0, 5)

-- Proven for this concrete program, by computation.
set_option maxRecDepth 100000 in
example : (after.regs 0, after.regs 1) = (0, 5) := by decide
