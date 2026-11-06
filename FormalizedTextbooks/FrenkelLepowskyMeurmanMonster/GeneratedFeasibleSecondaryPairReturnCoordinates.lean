/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPairTransition

/-! Original coordinate-pair addresses whose actual triality images remain
perpendicular to the first physical root. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The genuine coordinate-pair root formula at physical coordinates zero and one. -/
def generatedFeasiblePairOrthogonal (s : Fin 2) (ij : Fin 24 × Fin 24) : Prop :=
  (4 * (if (0 : Fin 24) = ij.1 then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) * (if (0 : Fin 24) = ij.2 then 1 else 0)) =
    (4 * (if (1 : Fin 24) = ij.1 then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) * (if (1 : Fin 24) = ij.2 then 1 else 0))

instance (s : Fin 2) (ij : Fin 24 × Fin 24) :
    Decidable (generatedFeasiblePairOrthogonal s ij) := inferInstanceAs (Decidable (_ = _))

/-- The physical formula is bound to the original preferred shortest-vector coordinates. -/
theorem generatedFeasiblePairOrthogonal_iff (s : Fin 2) (p : Fin 276) :
    generatedFeasiblePairOrthogonal s (griessCoordinatePair p) ↔
      griessShortIntegral (Sum.inl (s, p)) 0 = griessShortIntegral (Sum.inl (s, p)) 1 := Iff.rfl

/-- Finite original physical pair count, retaining both actual signed-short addresses. -/
def generatedFeasibleSecondaryPairReturnPhysicalCount : ℕ :=
  ∑ z : Fin 2 × griessCoordinatePairs × ZMod 2,
    if generatedFeasiblePairOrthogonal z.1 z.2.1.val ∧
      generatedFeasiblePairOrthogonal (if z.2.2 = 0 then 0 else 1) z.2.1.val then 1 else 0

set_option maxHeartbeats 4000000 in
-- Check all 1,104 original signed coordinate-pair addresses against the actual triality formula.
set_option maxRecDepth 10000 in
/-- Exactly 925 genuine signed coordinate-pair inputs and outputs are root perpendicular. -/
theorem generatedFeasibleSecondaryPairReturnPhysicalCount_eq :
    generatedFeasibleSecondaryPairReturnPhysicalCount = 925 := by
  decide +kernel

/-- Actual dictionary pair addresses returning to the perpendicular physical short catalogue. -/
def generatedFeasibleSecondaryPairReturnLabels : Finset (Fin 2 × Fin 276 × ZMod 2) :=
  Finset.univ.filter fun z =>
    generatedFeasiblePairOrthogonal z.1 (griessCoordinatePair z.2.1) ∧
      generatedFeasiblePairOrthogonal (if z.2.2 = 0 then 0 else 1)
        (griessCoordinatePair z.2.1)

/-- Transport through the original canonical pair equivalence gives exactly 925 actual addresses. -/
theorem generatedFeasibleSecondaryPairReturnLabels_card :
    generatedFeasibleSecondaryPairReturnLabels.card = 925 := by
  have hc : generatedFeasibleSecondaryPairReturnLabels.card =
      ∑ z : Fin 2 × Fin 276 × ZMod 2,
        if generatedFeasiblePairOrthogonal z.1 (griessCoordinatePair z.2.1) ∧
          generatedFeasiblePairOrthogonal (if z.2.2 = 0 then 0 else 1)
            (griessCoordinatePair z.2.1) then (1 : ℕ) else 0 := by
    simpa only [generatedFeasibleSecondaryPairReturnLabels, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun z : Fin 2 × Fin 276 × ZMod 2 =>
        generatedFeasiblePairOrthogonal z.1 (griessCoordinatePair z.2.1) ∧
          generatedFeasiblePairOrthogonal (if z.2.2 = 0 then 0 else 1)
            (griessCoordinatePair z.2.1)) Finset.univ).symm
  let e := Equiv.prodCongr (Equiv.refl (Fin 2))
    (Equiv.prodCongr griessCoordinatePairEquiv (Equiv.refl (ZMod 2)))
  have h := Equiv.sum_comp e (fun z : Fin 2 × griessCoordinatePairs × ZMod 2 =>
    if generatedFeasiblePairOrthogonal z.1 z.2.1.val ∧
      generatedFeasiblePairOrthogonal (if z.2.2 = 0 then 0 else 1) z.2.1.val
    then (1 : ℕ) else 0)
  rw [hc, ← generatedFeasibleSecondaryPairReturnPhysicalCount_eq]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
