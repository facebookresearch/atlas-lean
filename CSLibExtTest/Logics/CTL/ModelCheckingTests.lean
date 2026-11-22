/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.CTL.ModelChecking

@[expose] public section

namespace Cslib.CTL.ModelCheckingTests

/-- The toggle system: two states, each stepping to the other. -/
def mcToggleLTS : LTS Bool Unit where
  Tr b _ b' := b' = !b

/-- The unique atom holds exactly at `true`. -/
def mcToggleVal : Bool → Unit → Prop := fun b _ => b = true

instance (b : Bool) (μ : Unit) (b' : Bool) :
    Decidable (mcToggleLTS.Tr b μ b') :=
  inferInstanceAs (Decidable (b' = !b))

instance (b : Bool) (a : Unit) :
    Decidable (mcToggleVal b a) :=
  inferInstanceAs (Decidable (b = true))

example :
    check mcToggleLTS mcToggleVal false
      (.existsGlobally (.atom ())) = false := by
  decide

example :
    check mcToggleLTS mcToggleVal false
      (Formula.existsFinally (.atom ())) = true := by
  decide

example :
    check mcToggleLTS mcToggleVal true
      (.existsGlobally (.not (.atom ()))) = false := by
  decide

example :
    check mcToggleLTS mcToggleVal true
      (Formula.forallGlobally
        ((Formula.atom ()).or (.not (Formula.atom ())))) = true := by
  decide

example :
    check mcToggleLTS mcToggleVal false
      (Formula.forallFinally (.atom ())) = true := by
  decide

example :
    check mcToggleLTS mcToggleVal false
      (.forallUntil .top (.atom ())) = true := by
  decide

example :
    Decidable (Satisfies mcToggleLTS mcToggleVal true
      (.existsGlobally (.atom ()))) := inferInstance

/-- The diamond system on `Fin 4`: `0` branches to `1` and `2`, both
Tr to `3`, and `3` self-loops. -/
def mcDiamondLTS : LTS (Fin 4) Unit where
  Tr s _ t :=
    (s = 0 ∧ (t = 1 ∨ t = 2)) ∨ ((s = 1 ∨ s = 2) ∧ t = 3) ∨
      (s = 3 ∧ t = 3)

/-- The unique atom holds exactly at `3`. -/
def mcDiamondVal : Fin 4 → Unit → Prop := fun s _ => s = 3

instance (s : Fin 4) (μ : Unit) (t : Fin 4) :
    Decidable (mcDiamondLTS.Tr s μ t) :=
  inferInstanceAs (Decidable
    ((s = 0 ∧ (t = 1 ∨ t = 2)) ∨ ((s = 1 ∨ s = 2) ∧ t = 3) ∨
      (s = 3 ∧ t = 3)))

instance (s : Fin 4) (a : Unit) :
    Decidable (mcDiamondVal s a) :=
  inferInstanceAs (Decidable (s = 3))

example :
    check mcDiamondLTS mcDiamondVal 0
      (.existsUntil .top (.atom ())) = true := by
  decide

example :
    check mcDiamondLTS mcDiamondVal 0
      (.forallUntil .top (.atom ())) = true := by
  decide

example :
    check mcDiamondLTS mcDiamondVal 0
      (.existsGlobally (.not (.atom ()))) = false := by
  decide

example :
    sat mcDiamondLTS mcDiamondVal (.atom ()) = {3} := by
  decide

/-- The partially deadlocked system on `Fin 2`: state `0` self-loops
while state `1` has no successors. -/
def mcDeadLTS : LTS (Fin 2) Unit where
  Tr s _ t := s = 0 ∧ t = 0

/-- The unique atom holds exactly at `0`. -/
def mcDeadValAt0 : Fin 2 → Unit → Prop := fun s _ => s = 0

/-- The unique atom holds exactly at `1`. -/
def mcDeadValAt1 : Fin 2 → Unit → Prop := fun s _ => s = 1

instance (s : Fin 2) (μ : Unit) (t : Fin 2) :
    Decidable (mcDeadLTS.Tr s μ t) :=
  inferInstanceAs (Decidable (s = 0 ∧ t = 0))

instance (s : Fin 2) (a : Unit) :
    Decidable (mcDeadValAt0 s a) :=
  inferInstanceAs (Decidable (s = 0))

instance (s : Fin 2) (a : Unit) :
    Decidable (mcDeadValAt1 s a) :=
  inferInstanceAs (Decidable (s = 1))

/- The following four claims pin the maximal-path deadlock semantics
through the checker: at the deadlocked state `1`, `AF` and `AU` aiming
at `0` fail (the target is unreachable: there is no step at all), and
so does `EF`, while `AF` for an atom already holding at `1` succeeds.
A checker built on the classical `AU` duality without the deadlock
disjunct would wrongly report the first two as `true`. -/

example :
    check mcDeadLTS mcDeadValAt0 1
      (Formula.forallFinally (.atom ())) = false := by
  decide

example :
    check mcDeadLTS mcDeadValAt0 1
      (.forallUntil .top (.atom ())) = false := by
  decide

example :
    check mcDeadLTS mcDeadValAt0 1
      (Formula.existsFinally (.atom ())) = false := by
  decide

example :
    check mcDeadLTS mcDeadValAt1 1
      (Formula.forallFinally (.atom ())) = true := by
  decide

example :
    check mcDeadLTS mcDeadValAt0 0
      (Formula.forallFinally (.atom ())) = true := by
  decide

#print axioms Cslib.CTL.mem_sat
#print axioms Cslib.CTL.Satisfies.forallUntil_iff_not

end Cslib.CTL.ModelCheckingTests
