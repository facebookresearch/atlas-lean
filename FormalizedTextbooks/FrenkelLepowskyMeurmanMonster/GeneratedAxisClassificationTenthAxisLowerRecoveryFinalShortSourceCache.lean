/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortInputData

/-! Ungated final-cache bridge. The whole 98280-value finite certificate remains a hypothesis.
The reused Ninth module supplies catalogue addresses only; no Ninth action is invoked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete rational incoming matrix must be bound to the actual Root02 packet. -/
def GeneratedTenthFinalShortSourceMatrixCalibration
    (M : Matrix (Fin 24) (Fin 24) ℚ) : Prop :=
  ∀ i j, generatedAxisGlobalFifthRoot02Packet.1 i j = (M i j : ℝ)

/-- Executable array lookup includes every preferred short address and a zero default. -/
def generatedTenthFinalShortSourceCacheCoefficient (cache : Array ℤ) (r : GriessShortIndex) : ℤ :=
  cache[(generatedNinthLowerSpinShortAddress r).val]?.getD 0

/-- All catalogue values, including zeros, must equal the complete genuine final formula. -/
structure GeneratedTenthFinalShortSourceCacheCertificate
    (M : Matrix (Fin 24) (Fin 24) ℚ) (cache : Array ℤ) : Prop where
  length : cache.size = 98280
  values : ∀ a : Fin 98280,
    generatedTenthFinalShortSourceFormula M (generatedNinthLowerSpinShortIndex a) =
      (cache[a.val]?.getD 0 : ℚ)

/-- The full final Tenth short component equals the integer cache under explicit source bindings. -/
theorem generatedTenth_final_short_source_cache_actual
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : GeneratedTenthFinalShortSourceMatrixCalibration M)
    (cache : Array ℤ) (hcache : GeneratedTenthFinalShortSourceCacheCertificate M cache)
    (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceCacheCoefficient cache r : ℝ) := by
  have hc := hcache.values (generatedNinthLowerSpinShortAddress r)
  rw [generatedNinth_lower_spin_short_index_address] at hc
  unfold generatedTenthFinalShortSourceCacheCoefficient
  rw [generatedTenth_final_short_source_formula_actual hin M hm r, hc]
  norm_cast

/-- The cache's genuine physical normalization is exactly one over 128. -/
theorem generatedTenth_final_short_source_cache_coefficient
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : GeneratedTenthFinalShortSourceMatrixCalibration M)
    (cache : Array ℤ) (hcache : GeneratedTenthFinalShortSourceCacheCertificate M cache)
    (r : GriessShortIndex) :
    (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceCacheCoefficient cache r : ℝ) / 128 := by
  have h := generatedTenth_final_short_source_cache_actual hin M hm cache hcache r
  apply (eq_div_iff (by norm_num : (128 : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
