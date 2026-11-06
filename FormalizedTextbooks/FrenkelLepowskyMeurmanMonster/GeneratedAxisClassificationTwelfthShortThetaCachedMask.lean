/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSparseEquality

/-! The original complete preferred short masks retain their exact Parker cocode through the
checked cache. Every vector bit and the original preferred central section remain unchanged. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete preferred short masks use the exact cached original Parker cocode. -/
def generatedTwelfthShortThetaCachedMask : GriessShortIndex → ℕ
  | Sum.inl p => generatedAxisGlobalShortMask (Sum.inl p)
  | Sum.inr (Sum.inl (j, e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedAxisGlobalOctadCodeData j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (generatedTwelfthParkerThetaCache (generatedAxisGlobalOctadCodeData j))
        (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
          (trialityEvenMask e)))
  | Sum.inr (Sum.inr (d, j)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor d.val (generatedAxisGlobalOmegaMask (griessOddOmegaCoefficient d j)))
      (Nat.xor (generatedTwelfthParkerThetaCache ⟨d.val, by omega⟩)
        (generatedAxisGlobalCocodeColumnMask j))

/-- The cached evaluator equals the entire original sparse natural mask, including high bits. -/
theorem generatedTwelfth_short_theta_cached_sparse_actual (r : GriessShortIndex) :
    generatedTwelfthShortThetaCachedMask r = generatedAxisGlobalShortSparseMask r := by
  rcases r with p | (⟨j, e⟩ | ⟨d, j⟩)
  · rfl
  · simp only [generatedTwelfthShortThetaCachedMask, generatedAxisGlobalShortSparseMask,
      generatedTwelfth_parker_theta_cache_actual]
  · simp only [generatedTwelfthShortThetaCachedMask, generatedAxisGlobalShortSparseMask,
      generatedAxisGlobalShortMask, generatedTwelfth_parker_theta_cache_actual]

/-- Every cached preferred mask equals the entire original full natural mask. -/
theorem generatedTwelfth_short_theta_cached_actual (r : GriessShortIndex) :
    generatedTwelfthShortThetaCachedMask r = generatedAxisGlobalShortMask r := by
  rw [generatedTwelfth_short_theta_cached_sparse_actual,
    generatedNinth_lower_spin_short_sparse_mask_exact]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
