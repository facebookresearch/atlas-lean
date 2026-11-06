/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalShortCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry

/-! Actual local short-vector images preserve perpendicularity to the fixed first root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine dictionary address for the physical coordinate pair zero and one. -/
def generatedFeasiblePhysicalRootPair : Fin 276 :=
  griessCoordinatePairEquiv.symm ⟨(0, 1), by decide⟩

/-- The chosen dictionary address is bound to its actual two physical coordinates. -/
theorem generatedFeasiblePhysicalRootPair_coordinates :
    griessCoordinatePair generatedFeasiblePhysicalRootPair = (0, 1) :=
  congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply ⟨(0, 1), by decide⟩)

/-- The actual minus-pair integral root reads the difference of the two physical coordinates. -/
theorem generatedFeasiblePhysicalRoot_integral_pairing (r : GriessShortIndex) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
      (griessShortIntegral r) = 4 * (griessShortIntegral r 0 - griessShortIntegral r 1) := by
  have hi : griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      fun i => 4 * (if i = 0 then (1 : ℤ) else 0) +
        (-4) * (if i = 1 then (1 : ℤ) else 0) := by
    simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates, ite_true]
  rw [leechIntegralPairing, hi]
  simp only [add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Physical root perpendicularity is exactly the original catalogue coordinate condition. -/
theorem generatedFeasiblePhysicalRoot_orthogonal_iff (r : GriessShortIndex) :
    stdPairingFun (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
      (griessShortVector r) = 0 ↔ griessShortIntegral r 0 = griessShortIntegral r 1 := by
  rw [griessShortVector_pairing, generatedFeasiblePhysicalRoot_integral_pairing]
  simp only [div_eq_zero_iff, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]
  norm_num
  simp only [sub_eq_zero, Int.cast_inj]

/-- The original plus-pair root is perpendicular to the fixed minus-pair root. -/
theorem generatedFeasiblePhysicalRoot_plus_orthogonal :
    stdPairingFun (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
      (griessShortVector (Sum.inl (1, generatedFeasiblePhysicalRootPair))) = 0 := by
  rw [generatedFeasiblePhysicalRoot_orthogonal_iff]
  norm_num [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]

/-- Any original isometry fixing the first short class preserves perpendicularity
of its plus-pair image, including the possible signs of both physical representatives. -/
theorem generatedFeasiblePhysicalRoot_image_orthogonal (e : leechIsomSubgroup)
    (he : griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    griessShortIntegral (griessShortPermutation e
      (Sum.inl (1, generatedFeasiblePhysicalRootPair))) 0 =
      griessShortIntegral (griessShortPermutation e
        (Sum.inl (1, generatedFeasiblePhysicalRootPair))) 1 := by
  rw [← generatedFeasiblePhysicalRoot_orthogonal_iff]
  have hp := e.property.1
    (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
    (griessShortVector (Sum.inl (1, generatedFeasiblePhysicalRootPair)))
  rw [generatedFeasiblePhysicalRoot_plus_orthogonal] at hp
  rcases griessShortPermutation_vector e (Sum.inl (0, generatedFeasiblePhysicalRootPair))
    with h0 | h0 <;>
    rcases griessShortPermutation_vector e (Sum.inl (1, generatedFeasiblePhysicalRootPair))
      with h1 | h1
  all_goals
    rw [h0, h1, he] at hp
    simpa only [stdPairingFun, Pi.neg_apply, neg_mul, mul_neg, neg_neg,
      Finset.sum_neg_distrib, neg_eq_zero] using hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
