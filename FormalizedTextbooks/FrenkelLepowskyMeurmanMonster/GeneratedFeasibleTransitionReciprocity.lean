/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
    FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionActualFibers

/-! Genuine weighted symmetry for all actual local-orbit transition coset counts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original triality transitions obey weighted reciprocity for every pair of actual first-axis
    stabilizer orbits. -/
theorem generatedFeasibleActualTransition_reciprocity (p : Fin 276) (a b : GriessSpace) :
    Nat.card (MulAction.orbit (localAxisStabilizer p) a) * Nat.card
        (generatedFeasibleActualTransitionCosets p a b) =
      Nat.card (MulAction.orbit (localAxisStabilizer p) b) * Nat.card
          (generatedFeasibleActualTransitionCosets p b a) := by
  have ha := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (localAxisStabilizer p) a)
  have hb := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (localAxisStabilizer p) b)
  rw [Nat.card_prod] at ha hb
  have hab := generatedFeasibleActualTransition_fiber_balance p a b
  have hba := generatedFeasibleActualTransition_fiber_balance p b a
  have he :
      (Nat.card (MulAction.orbit (localAxisStabilizer p) a) * Nat.card
          (generatedFeasibleActualTransitionCosets p a b)) *
          Nat.card (localFeasibleTransitionSubgroup p) =
        (Nat.card (MulAction.orbit (localAxisStabilizer p) b) * Nat.card
            (generatedFeasibleActualTransitionCosets p b a)) *
          Nat.card (localFeasibleTransitionSubgroup p) := by
    calc
      _ = Nat.card (MulAction.orbit (localAxisStabilizer p) a) *
          (Nat.card (generatedFeasibleActualTransitionCosets p a b) * Nat.card
              (localFeasibleTransitionSubgroup p)) :=
        Nat.mul_assoc _ _ _
      _ = Nat.card (MulAction.orbit (localAxisStabilizer p) a) *
          (Nat.card (generatedFeasibleTransitionVectors p a b) * Nat.card (MulAction.stabilizer
              (localAxisStabilizer p) a)) :=
        congrArg (Nat.card (MulAction.orbit (localAxisStabilizer p) a) * ·) hab
      _ = Nat.card (generatedFeasibleTransitionVectors p a b) * Nat.card (localAxisStabilizer
          p) := by
        rw [← ha]
        ring
      _ = Nat.card (generatedFeasibleTransitionVectors p b a) * Nat.card (localAxisStabilizer
          p) := by
        rw [generatedFeasibleTransition_vectors_card_reverse p]
      _ = Nat.card (MulAction.orbit (localAxisStabilizer p) b) *
          (Nat.card (generatedFeasibleTransitionVectors p b a) *
            Nat.card (MulAction.stabilizer (localAxisStabilizer p) b)) := by
        rw [← hb]
        ring
      _ = Nat.card (MulAction.orbit (localAxisStabilizer p) b) *
          (Nat.card (generatedFeasibleActualTransitionCosets p b a) * Nat.card
              (localFeasibleTransitionSubgroup p)) :=
        congrArg (Nat.card (MulAction.orbit (localAxisStabilizer p) b) * ·) hba.symm
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have hn : 0 < Nat.card (localFeasibleTransitionSubgroup p) := by
    rw [Nat.card_congr (localFeasibleTransitionEquiv p).toEquiv,
      localOmegaAxisIntersection_card]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right hn he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
