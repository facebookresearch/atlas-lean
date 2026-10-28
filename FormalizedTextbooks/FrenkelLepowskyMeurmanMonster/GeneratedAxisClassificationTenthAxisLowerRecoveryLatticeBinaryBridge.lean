/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Actual physical numerator binding and complete integral basis certificates imply
actual binary compatibility. No arbitrary original spin-word comparison is required. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every retained original denominator is a genuine positive normalization. -/
theorem generatedTenth_axis_lower_recovery_compact_denominator_ne_zero :
    ∀ g : Fin 11, generatedTenthAxisLowerRecoveryCompactSpatialDenominator g ≠ 0 := by
  decide +kernel

/-- The actual whole physical isometry induces exactly its certified integral-basis action. -/
theorem generatedTenth_axis_lower_recovery_spatial_binary_of_basis
    (g : Fin 11) (C : Matrix (Fin 24) (Fin 24) ℤ)
    (hphysical : generatedTenthAxisLowerRecoveryCompactPhysicalCondition g)
    (hbasis : generatedTenthAxisLowerRecoveryCompactSpatialNumerator g * leechBasisMatrix =
      (generatedTenthAxisLowerRecoveryCompactSpatialDenominator g : ℤ) •
        (leechBasisMatrix * C))
    (hbinary : ∀ j : Fin 24,
      (leechHyperbolicInverse * C.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
            monsterCo1GeometryBinaryMaskDecode
              (generatedTenthAxisLowerRecoveryCompactBinaryColumns g j)) :
    generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g := by
  intro j
  rw [generatedTwelfth_spatial_binary_of_matrix
    (generatedTenthAxisLowerRecoveryCompactSpatial g)
    (generatedTenthAxisLowerRecoveryCompactSpatialNumerator g) C
    (generatedTenthAxisLowerRecoveryCompactSpatialDenominator g)
    (generatedTenth_axis_lower_recovery_compact_denominator_ne_zero g)
    hphysical hbasis]
  exact hbinary j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
