/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceFormulaGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCacheActual

/-! Exact whole-codeword caches retain both original Ninth tensor source contributions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete original tensor numerator, using verified whole Golay masks and weight signs. -/
def generatedNinthLowerTensorSourceCachedInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (generatedTwelfthGolayMaskCache d).testBit i.val then -1 else 1
  let parker := generatedTwelfthGolayPhaseCache d
  (if n.val < 2048 then 4 else -4) * sigma * generatedNinthLowerIncomingCoefficient d i +
    sigma * parker * (generatedNinthMiddleNumerator ⟨d.val, by omega⟩ i -
      generatedNinthMiddleNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every label and spatial column retains the complete original integer source formula. -/
theorem generatedNinth_lower_tensor_source_cached_actual (n : Fin 4096) (i : Fin 24) :
    generatedNinthLowerTensorSourceCachedInteger n i =
      generatedNinthLowerTensorSourceInteger n i := by
  simp only [generatedNinthLowerTensorSourceCachedInteger, generatedNinthLowerTensorSourceInteger,
    generatedTwelfth_golay_mask_cache_actual, generatedTwelfth_golay_phase_cache_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
