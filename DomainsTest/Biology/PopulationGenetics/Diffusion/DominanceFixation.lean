/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.DominanceFixation

/-! Tests for the dominance specializations of Kimura's fixation formula: the genic
identification at an interior frequency and at the endpoints, the neutral case, and the
recessive and dominant integral ratios. -/

open Real Set

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.DominanceFixation

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Genic identification at an interior frequency: `h = 1 / 2` is Kimura's formula. -/
example (c : ℝ) :
    fixationProb (dominanceDrift c (1 / 2)) (fun x => x * (1 - x)) (1 / 2) =
      kimuraFixation c (1 / 2) :=
  fixationProb_dominance_half c ⟨by norm_num, by norm_num⟩

/-- Genic endpoint: an absent allele is never fixed. -/
example (c : ℝ) : fixationProb (dominanceDrift c (1 / 2)) (fun x => x * (1 - x)) 0 = 0 := by
  rw [fixationProb_dominance_half c ⟨le_rfl, zero_le_one⟩]
  exact kimuraFixation_zero_right c

/-- Genic endpoint: an already fixed allele stays fixed. -/
example (c : ℝ) : fixationProb (dominanceDrift c (1 / 2)) (fun x => x * (1 - x)) 1 = 1 := by
  rw [fixationProb_dominance_half c ⟨zero_le_one, le_rfl⟩]
  exact kimuraFixation_one_right c

/-- Neutral case at an interior frequency with a nonstandard dominance coefficient. -/
example : fixationProb (dominanceDrift 0 2) (fun x => x * (1 - x)) (1 / 3) = 1 / 3 :=
  fixationProb_dominance_zero_c 2 ⟨by norm_num, by norm_num⟩

/-- Recessive case at an interior frequency, in the theorem's integral form. -/
example (c : ℝ) :
    fixationProb (dominanceDrift c 0) (fun x => x * (1 - x)) (1 / 2) =
      (∫ x in (0 : ℝ)..(1 / 2), exp (-2 * c * x ^ 2)) /
        ∫ x in (0 : ℝ)..1, exp (-2 * c * x ^ 2) :=
  fixationProb_dominance_zero_h c ⟨by norm_num, by norm_num⟩

/-- Dominant case at an interior frequency, in the theorem's integral form. -/
example (c : ℝ) :
    fixationProb (dominanceDrift c 1) (fun x => x * (1 - x)) (1 / 2) =
      (∫ x in (0 : ℝ)..(1 / 2), exp (2 * c * x ^ 2 - 4 * c * x)) /
        ∫ x in (0 : ℝ)..1, exp (2 * c * x ^ 2 - 4 * c * x) :=
  fixationProb_dominance_one_h c ⟨by norm_num, by norm_num⟩

/-- At zero scaled selection the genic specialization overlaps neutrality. -/
example : fixationProb (dominanceDrift 0 (1 / 2)) (fun x => x * (1 - x)) (1 / 2) = 1 / 2 := by
  rw [fixationProb_dominance_half 0 ⟨by norm_num, by norm_num⟩]
  exact kimuraFixation_neutral _

/-- Recessive endpoint: at `p = 0` the numerator integral is over an empty range. -/
example (c : ℝ) : fixationProb (dominanceDrift c 0) (fun x => x * (1 - x)) 0 = 0 := by
  rw [fixationProb_dominance_zero_h c ⟨le_rfl, zero_le_one⟩,
    intervalIntegral.integral_same, zero_div]

#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance_half
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance_zero_h
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance_one_h
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance_zero_c

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.DominanceFixation
