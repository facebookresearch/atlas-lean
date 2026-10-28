/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCoordinates

/-! Original physical short-coordinate checks for the feasible finite geometry.
The fixed norm-four root has coordinates 4(e₀-e₁), so orthogonality means
equality of coordinates zero and one. No Ω orbit identification is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The original signed coordinate-pair representatives orthogonal to 4(e₀-e₁). -/
def generatedFeasibleOrthogonalPairLabels : Finset (Fin 2 × Fin 276) :=
  Finset.univ.filter fun z =>
    griessShortIntegral (Sum.inl z) 0 = griessShortIntegral (Sum.inl z) 1

/-- Finite coordinate-pair count before transport through the canonical pair equivalence. -/
def generatedFeasibleOrthogonalPairPhysicalCount : ℕ :=
  ∑ z : Fin 2 × griessCoordinatePairs,
    if (4 * (if (0 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (0 : Fin 24) = z.2.val.2 then 1 else 0)) =
      (4 * (if (1 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (1 : Fin 24) = z.2.val.2 then 1 else 0))
    then 1 else 0

set_option maxHeartbeats 4000000 in
-- Check 552 original increasing coordinate pairs and both sign families.
set_option maxRecDepth 10000 in
/-- There are 463 original coordinate-pair lines perpendicular to the fixed root. -/
theorem generatedFeasibleOrthogonalPairPhysicalCount_eq :
    generatedFeasibleOrthogonalPairPhysicalCount = 463 := by
  decide +kernel

/-- Transport through the genuine canonical pair equivalence preserves the finite count. -/
theorem generatedFeasibleOrthogonalPairLabels_card :
    generatedFeasibleOrthogonalPairLabels.card = 463 := by
  have hc : generatedFeasibleOrthogonalPairLabels.card =
      ∑ z : Fin 2 × Fin 276, if griessShortIntegral (Sum.inl z) 0 =
        griessShortIntegral (Sum.inl z) 1 then (1 : ℕ) else 0 := by
    simpa only [generatedFeasibleOrthogonalPairLabels, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun z : Fin 2 × Fin 276 =>
        griessShortIntegral (Sum.inl z) 0 = griessShortIntegral (Sum.inl z) 1)
        Finset.univ).symm
  rw [hc]
  let e := Equiv.prodCongr (Equiv.refl (Fin 2)) griessCoordinatePairEquiv
  have h := Equiv.sum_comp e (fun z : Fin 2 × griessCoordinatePairs =>
    if (4 * (if (0 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (0 : Fin 24) = z.2.val.2 then 1 else 0)) =
      (4 * (if (1 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (1 : Fin 24) = z.2.val.2 then 1 else 0))
    then (1 : ℕ) else 0)
  change _ = generatedFeasibleOrthogonalPairPhysicalCount at h
  change _ = 463
  rw [← generatedFeasibleOrthogonalPairPhysicalCount_eq]
  exact h

/-- Canonical half-codeword labels whose signs at the first two coordinates agree. -/
def generatedFeasibleOddEqualSignCodes : Finset (Fin 2048) :=
  Finset.univ.filter fun d =>
    (golayEncodedMask d.val).testBit 0 = (golayEncodedMask d.val).testBit 1

set_option maxHeartbeats 4000000 in
-- Check the 2,048 original half-codewords against the two actual physical coordinates.
set_option maxRecDepth 10000 in
/-- Exactly half of the original 2,048 half-codewords have the required physical signs. -/
theorem generatedFeasibleOddEqualSignCodes_card :
    generatedFeasibleOddEqualSignCodes.card = 1024 := by
  decide +kernel

/-- An odd shortest representative is perpendicular precisely when its distinguished
coordinate is outside the root pair and its original codeword signs there agree. -/
theorem generatedFeasibleOdd_orthogonal_iff (d : Fin 2048) (j : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (d, j))) 0 =
      griessShortIntegral (Sum.inr (Sum.inr (d, j))) 1 ↔
      j ≠ 0 ∧ j ≠ 1 ∧ d ∈ generatedFeasibleOddEqualSignCodes := by
  have h (b0 b1 : Bool) :
      (if b0 then (-1 : ℤ) else 1) * (if (0 : Fin 24) = j then -3 else 1) =
        (if b1 then (-1 : ℤ) else 1) * (if (1 : Fin 24) = j then -3 else 1) ↔
        j ≠ 0 ∧ j ≠ 1 ∧ b0 = b1 := by
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
      cases b0 <;> cases b1 <;> simp_all [eq_comm]
  simpa only [griessShortIntegral, generatedFeasibleOddEqualSignCodes,
    Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one] using
      h ((golayEncodedMask d.val).testBit 0) ((golayEncodedMask d.val).testBit 1)

/-- All original odd representatives perpendicular to the fixed physical root. -/
def generatedFeasibleOrthogonalOddLabels : Finset (Fin 2048 × Fin 24) :=
  generatedFeasibleOddEqualSignCodes ×ˢ ((Finset.univ.erase 0).erase 1)

/-- The finite product is exactly the original odd-coordinate orthogonality condition. -/
theorem generatedFeasibleOrthogonalOddLabels_mem (d : Fin 2048) (j : Fin 24) :
    (d, j) ∈ generatedFeasibleOrthogonalOddLabels ↔
      griessShortIntegral (Sum.inr (Sum.inr (d, j))) 0 =
        griessShortIntegral (Sum.inr (Sum.inr (d, j))) 1 := by
  rw [generatedFeasibleOdd_orthogonal_iff]
  simp only [generatedFeasibleOrthogonalOddLabels, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hd, hj1, hj0⟩
    exact ⟨hj0, hj1, hd⟩
  · rintro ⟨hj0, hj1, hd⟩
    exact ⟨hd, hj1, hj0⟩

/-- There are 22,528 original odd short-vector lines perpendicular to the fixed root. -/
theorem generatedFeasibleOrthogonalOddLabels_card :
    generatedFeasibleOrthogonalOddLabels.card = 22528 := by
  rw [generatedFeasibleOrthogonalOddLabels, Finset.card_product,
    generatedFeasibleOddEqualSignCodes_card]
  have hc : ((Finset.univ : Finset (Fin 24)).erase 0 |>.erase 1).card = 22 := by decide
  rw [hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
