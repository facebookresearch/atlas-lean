/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthShortThetaCachedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinOctadBalancedCatalogue

/-! The original complete preferred short masks retain their exact Parker cocode through the
checked cache. Every vector bit and the original preferred central section remain unchanged. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete preferred short masks use the exact cached original Parker cocode. -/
def generatedNinthLowerSpinShortBalancedMask : GriessShortIndex → ℕ
  | Sum.inl p => generatedAxisGlobalShortMask (Sum.inl p)
  | Sum.inr (Sum.inl (j, e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedNinthLowerSpinOctadCodeBalanced j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (generatedTwelfthParkerThetaCache (generatedNinthLowerSpinOctadCodeBalanced j))
        (generatedAxisGlobalSparseCocodeMask (generatedNinthLowerSpinOctadCoordinatesBalanced j)
          (trialityEvenMask e)))
  | Sum.inr (Sum.inr (d, j)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor d.val (generatedAxisGlobalOmegaMask (griessOddOmegaCoefficient d j)))
      (Nat.xor (generatedTwelfthParkerThetaCache ⟨d.val, by omega⟩)
        (generatedAxisGlobalCocodeColumnMask j))

/-- Balanced lookup retains the complete preferred mask
of the original theta-cached evaluator. -/
theorem generatedNinth_lower_spin_short_balanced_mask_theta_actual (r : GriessShortIndex) :
    generatedNinthLowerSpinShortBalancedMask r = generatedTwelfthShortThetaCachedMask r := by
  rcases r with p | (⟨j, e⟩ | ⟨d, j⟩)
  · rfl
  · simp only [generatedNinthLowerSpinShortBalancedMask, generatedTwelfthShortThetaCachedMask,
      generatedNinth_lower_spin_octad_code_balanced_actual,
      generatedNinth_lower_spin_octad_coordinates_balanced_actual]
  · rfl

/-- Every bit of every original preferred natural mask is retained,
including the original central section. -/
theorem generatedNinth_lower_spin_short_balanced_mask_actual (r : GriessShortIndex) :
    generatedNinthLowerSpinShortBalancedMask r = generatedAxisGlobalShortMask r :=
  (generatedNinth_lower_spin_short_balanced_mask_theta_actual r).trans
    (generatedTwelfth_short_theta_cached_actual r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
