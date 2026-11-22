/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.CTL.Basic

@[expose] public section

namespace Cslib.CTL.BasicTests

/-- The toggle system: two states, each stepping to the other. -/
def toggleLTS : LTS Bool Unit where
  Tr b _ b' := b' = !b

/-- The unique atom holds exactly at `true`. -/
def toggleVal : Bool → Unit → Prop := fun b _ => b = true

/-- The toggle system is serial: every state steps to the other. -/
theorem toggleSerial : Serial toggleLTS := fun b => ⟨(), !b, rfl⟩

/-- The alternating run of the toggle system, starting at `true`. -/
def alternating : ℕ → Bool
  | 0 => true
  | n + 1 => !(alternating n)

example : Satisfies toggleLTS toggleVal true (.existsGlobally .top) :=
  ⟨alternating, rfl, fun _ => ⟨(), rfl⟩, fun _ => trivial⟩

example : Satisfies toggleLTS toggleVal false
    (Formula.existsFinally (.atom ())) := by
  rw [Satisfies.existsFinally_iff_reachable]
  exact ⟨true, ⟨[()], .stepL rfl .refl⟩, rfl⟩

example : Satisfies toggleLTS toggleVal false (.existsNext (.atom ())) :=
  ⟨(), true, rfl, rfl⟩

example : Satisfies toggleLTS toggleVal false
    (Formula.forallNext (.atom ())) := by
  rw [Satisfies.forallNext_iff]
  intro _ _ hstep
  exact hstep

example : Satisfies toggleLTS toggleVal true
    (Formula.forallGlobally
      ((Formula.atom ()).or (.not (Formula.atom ())))) := by
  rw [Satisfies.forallGlobally_iff_reachable]
  intro t _
  rw [Satisfies.or_iff]
  cases t with
  | false => exact Or.inr (fun h => by cases h)
  | true => exact Or.inl rfl

example : ¬Satisfies toggleLTS toggleVal true
    (Formula.forallGlobally (.atom ())) := by
  rw [Satisfies.forallGlobally_iff_reachable]
  intro h
  have hfalse := h false ⟨[()], .stepL rfl .refl⟩
  cases hfalse

example : Satisfies toggleLTS toggleVal false
    (Formula.forallFinally (.atom ())) := by
  rw [Satisfies.forallFinally_iff_not_existsGlobally_not_of_serial
    toggleSerial]
  intro hEG
  obtain ⟨ss, h0, hrun, hall⟩ := hEG
  obtain ⟨label, hstep⟩ := hrun 0
  have h1 : ss 1 = true := by
    rw [h0] at hstep
    exact hstep
  exact hall 1 h1

/-- The counter system: natural numbers stepping to their successor. -/
def counterLTS : LTS Nat Unit where
  Tr n _ m := m = n + 1

/-- The atom `a` holds exactly at the state `a`. -/
def counterVal : Nat → Nat → Prop := fun n a => n = a

/-- The counter system is serial: every state steps to its successor. -/
theorem counterSerial : Serial counterLTS :=
  fun n => ⟨(), n + 1, rfl⟩

example : Satisfies counterLTS counterVal 0
    (Formula.existsFinally (.atom 5)) := by
  rw [Satisfies.existsFinally_iff_reachable]
  exact ⟨5, ⟨[(), (), (), (), ()],
    .stepL rfl (.stepL rfl (.stepL rfl (.stepL rfl (.stepL rfl .refl))))⟩,
    rfl⟩

example : Satisfies counterLTS counterVal 0 (.existsGlobally .top) :=
  ⟨fun n => n, rfl, fun _ => ⟨(), rfl⟩, fun _ => trivial⟩

/-- The deadlocked system: a single state with no transitions. -/
def deadlockLTS : LTS Unit Unit where
  Tr _ _ _ := False

/-- No atom holds at the deadlocked state. -/
def deadlockVal : Unit → Unit → Prop := fun _ _ => False

/-- The unique atom holds at the deadlocked state. -/
def deadlockValTrue : Unit → Unit → Prop := fun _ _ => True

/-- The unique state of `deadlockLTS` is deadlocked. -/
theorem deadlock_dead :
    ∀ label t, ¬deadlockLTS.Tr () label t := by
  simp [deadlockLTS]

example (φ : Formula Unit) :
    Satisfies deadlockLTS deadlockVal () (Formula.forallNext φ) := by
  rw [Satisfies.forallNext_iff]
  intro _ _ hstep
  cases hstep

example (φ : Formula Unit) :
    ¬Satisfies deadlockLTS deadlockVal () (.existsNext φ) := by
  simp [deadlockLTS]

example (φ : Formula Unit) :
    Satisfies deadlockLTS deadlockVal () (Formula.existsFinally φ) ↔
      Satisfies deadlockLTS deadlockVal () φ := by
  rw [Satisfies.existsFinally_iff_reachable]
  constructor
  · rintro ⟨t, -, hφ⟩
    cases t
    exact hφ
  · intro hφ
    exact ⟨(), LTS.CanReach.refl _ _, hφ⟩

/- Deadlock regression: under the classical `AU`/`AF` duality
translations, `A[⊤ U ψ]` and `AF ψ` below would hold at this deadlocked
state although `ψ` is false there and no step can reach a `ψ`-state.
With maximal-path semantics, `AU` and `AF` at a deadlock reduce to
their target formula. -/
example : ¬Satisfies deadlockLTS deadlockVal ()
    (.forallUntil (.atom ()) (.atom ())) := by
  rw [Satisfies.forallUntil_deadlock deadlock_dead]
  simp [deadlockVal]

example : ¬Satisfies deadlockLTS deadlockVal ()
    (.forallUntil .top (.atom ())) := by
  rw [Satisfies.forallUntil_deadlock deadlock_dead]
  simp [deadlockVal]

example : Satisfies deadlockLTS deadlockValTrue ()
    (.forallUntil Formula.bot (.atom ())) := by
  rw [Satisfies.forallUntil_deadlock deadlock_dead]
  simp [deadlockValTrue]

example : ¬Satisfies deadlockLTS deadlockVal ()
    (Formula.forallFinally (.atom ())) := by
  rw [Satisfies.forallFinally_deadlock deadlock_dead]
  simp [deadlockVal]

example : Satisfies deadlockLTS deadlockValTrue ()
    (Formula.forallFinally (.atom ())) := by
  rw [Satisfies.forallFinally_deadlock deadlock_dead]
  simp [deadlockValTrue]

#print axioms Satisfies.existsFinally_eq_lfp
#print axioms Satisfies.existsGlobally_eq_gfp
#print axioms Satisfies.forallUntil_iff_classical_of_serial

end Cslib.CTL.BasicTests
