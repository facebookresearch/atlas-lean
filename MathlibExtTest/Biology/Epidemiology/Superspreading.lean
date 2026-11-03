/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.Superspreading

/-!
# Tests for negative-binomial superspreading

Non-vacuity witness: `R = 2`, `k = 1` (geometric offspring) is a probability law whose
extinction probability is at most `1/2`, because `1/2` is a fixed point of
`G_1(s) = 1 / (1 + 2 (1 - s))`. The dispersion comparison at `k = 1/2` versus `k = 1`.
Boundary cases: `R = 0` puts all mass at `0`; `k = 0` is outside the domain and the total
`rpow` gives the junk generating function `1`.
-/

@[expose] public section

open Set MathlibExt.Probability.GaltonWatson

namespace MathlibExtTest.Biology.Epidemiology.Superspreading

open MathlibExt.Biology.Epidemiology.Superspreading

-- Geometric case: `G_1(s) = 1 / (1 + 2 (1 - s))`, and `1/2` is a fixed point.
example : nbPgf 2 1 (1 / 2) = 1 / 2 := by rw [nbPgf_one_dispersion]; norm_num

-- Non-vacuity witness: the extinction probability for `R = 2`, `k = 1` is at most `1/2`.
example :
    haveI := isProbabilityMeasure_nbOffspring (R := 2) (k := 1) one_pos (by norm_num)
    extinctionProb (nbOffspring 2 1) ≤ 1 / 2 := by
  have := isProbabilityMeasure_nbOffspring (R := 2) (k := 1) one_pos (by norm_num)
  exact (isLeast_extinctionProb_nbOffspring one_pos (by norm_num)).2
    ⟨⟨by norm_num, by norm_num⟩, by rw [nbPgf_one_dispersion]; norm_num⟩

-- Stronger superspreading (`k = 1/2`) gives at least the extinction probability of `k = 1`.
example :
    haveI := isProbabilityMeasure_nbOffspring (R := 2) (k := 1 / 2) (by norm_num) (by norm_num)
    haveI := isProbabilityMeasure_nbOffspring (R := 2) (k := 1) one_pos (by norm_num)
    extinctionProb (nbOffspring 2 1) ≤ extinctionProb (nbOffspring 2 (1 / 2)) :=
  extinctionProb_nbOffspring_antitone (by norm_num) (by norm_num) (by norm_num)

-- Boundary `R = 0`: no secondary cases, `P(Z = 0) = 1` and `P(Z = 1) = 0`.
example : nbPmf 0 1 0 = 1 := by simp [nbPmf]
example : nbPmf 0 1 1 = 0 := by simp [nbPmf]

-- Junk value outside the domain `k > 0`: `G_0 ≡ 1`.
example (R s : ℝ) : nbPgf R 0 s = 1 := by simp [nbPgf]

end MathlibExtTest.Biology.Epidemiology.Superspreading
