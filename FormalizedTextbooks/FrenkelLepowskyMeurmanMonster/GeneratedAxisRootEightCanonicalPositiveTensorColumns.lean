/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveAxis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorVectorReplay
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorColumns

/-! Complete canonical tensor coordinates follow from genuinely certified full source columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The full canonical output numerator retains every physical source column. -/
def generatedRootEightCanonicalPositiveTensorNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, generatedRootEightCanonicalTensorSpinInteger j n *
    generatedRootEightCanonicalSpatialNumerator i j

/-- Every actual positive canonical tensor entry is the defining full spin and spatial column sum. -/
theorem generatedRootEight_canonical_positive_tensor_columns (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal generatedRootEightCanonicalPositiveLocal x)).2.2 t i =
      ∑ j : Fin 24, (generatedRootEightCompactSpin 12).val
        (fun u => (griessConwayEncode x).2.2 u j) t *
          ((generatedRootEightCanonicalSpatialNumerator i j : ℝ) / 4) := by
  change (griessConwayEncode
    (localGriessRepresentation generatedRootEightCanonicalPositiveFiber x)).2.2 t i = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
    generatedAxisGlobalTensor_local_coordinate]
  simp only [generatedRootEightCanonicalPositiveFiber,
    generatedRootEight_canonical_spatial_unit]

/-- Full integer replay of every genuine source column gives the complete canonical normalization. -/
theorem generatedRootEight_canonical_positive_tensor_normalization (x : GriessSpace)
    (v : Fin 24 → NortonUIntegerVector) (D : ℝ)
    (hs : ∀ j t, (griessConwayEncode x).2.2 t j =
      (v j (nortonUIntegerLabel t) : ℝ) / D)
    (hr : ∀ j, (generatedRootEightCompactSpin 12).val
      ((16 : ℝ) • nortonUIntegerEmbed (v j)) =
        nortonUIntegerEmbed (generatedRootEightCanonicalTensorSpinInteger j))
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal generatedRootEightCanonicalPositiveLocal x)).2.2 t i =
      (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
        (64 * D) := by
  have hc (j : Fin 24) :
      (fun u => (griessConwayEncode x).2.2 u j) =
        (1 / D : ℝ) • nortonUIntegerEmbed (v j) := by
    ext u
    simp only [hs, Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
    ring
  have hn (j : Fin 24) : (generatedRootEightCompactSpin 12).val
      (nortonUIntegerEmbed (v j)) t =
      (generatedRootEightCanonicalTensorSpinInteger j (nortonUIntegerLabel t) : ℝ) / 16 := by
    have ht := congrFun (hr j) t
    rw [map_smul] at ht
    simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed] at ht
    linarith
  rw [generatedRootEight_canonical_positive_tensor_columns]
  simp_rw [hc, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, hn,
    generatedRootEightCanonicalPositiveTensorNumerator,
    Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
