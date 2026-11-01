/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortPackedCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingTensorPackedCache

/-! Ungated numerical candidate data/helper draft. Discovery is not a source proof. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A whole function-valued cache must bind every98280 original final formula value. -/
def GeneratedTenthFinalShortFunctionCacheCondition
    (M : Matrix (Fin 24) (Fin 24) ℚ) (cache : Fin 98280 → ℤ) : Prop :=
  ∀ a : Fin 98280,
    generatedTenthFinalShortSourceFormula M (generatedNinthLowerSpinShortIndex a) =
      (cache a : ℚ)

/-- Whole finite source equality binds every actual final coefficient, including all zeros. -/
theorem generatedTenth_final_short_function_cache_actual
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : GeneratedTenthFinalShortSourceMatrixCalibration M)
    (cache : Fin 98280 → ℤ) (hcache : GeneratedTenthFinalShortFunctionCacheCondition M cache)
    (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (cache (generatedNinthLowerSpinShortAddress r) : ℝ) := by
  have hc := hcache (generatedNinthLowerSpinShortAddress r)
  rw [generatedNinth_lower_spin_short_index_address] at hc
  rw [generatedTenth_final_short_source_formula_actual hin M hm r, hc]
  norm_cast

/-- Exact incoming B/64 source calibration and all final finite values remain separate. -/
theorem generatedTenth_final_short_function_cache_of_tensor
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hB : GeneratedTenthFinalShortSourceTensorCalibration generatedTenthIncomingTensorPackedCache)
    (cache : Fin 98280 → ℤ)
    (hvalues : ∀ a : Fin 98280,
      generatedTenthFinalShortSourceCalibratedFormula M generatedTenthIncomingTensorPackedCache
          (generatedNinthLowerSpinShortIndex a) = (cache a : ℚ)) :
    GeneratedTenthFinalShortFunctionCacheCondition M cache := by
  intro a
  rw [generatedTenth_final_short_source_calibrated_formula M
    generatedTenthIncomingTensorPackedCache hB]
  exact hvalues a

/-- Discovery data becomes the actual final packed cache only after the whole source certificate. -/
theorem generatedTenth_final_short_packed_cache_actual
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : GeneratedTenthFinalShortSourceMatrixCalibration M)
    (hcache : GeneratedTenthFinalShortFunctionCacheCondition M
      generatedTenthFinalShortPackedCacheAddressValue) (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortPackedCacheCoefficient r : ℝ) := by
  exact generatedTenth_final_short_function_cache_actual hin M hm
    generatedTenthFinalShortPackedCacheAddressValue hcache r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
