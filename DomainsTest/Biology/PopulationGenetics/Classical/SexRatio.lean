/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.SexRatio

/-!
# Tests for Fisher's sex-ratio principle

At a female-biased resident ratio a son-biased mutant wins, and at a male-biased resident
ratio a daughter-biased mutant wins. With sons twice as costly as daughters, equal investment
produces one son for every two daughters.
-/

@[expose] public section

open Set
open MathlibExt.Biology.PopulationGenetics.Classical.SexRatio

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.SexRatio

-- Acceptance 1: `W(m', 1/2)` is constant in `m'`.
example (x x' : ℝ) : W x (1 / 2) = W x' (1 / 2) := by rw [W_half_right, W_half_right]

-- Acceptance 2 (stated variant): sons twice as costly as daughters gives one son per two
-- daughters at the stable equal investment.
example : sonFraction 2 1 (1 / 2) = 1 / 3 := by
  rw [sonFraction_half (by norm_num) (by norm_num)]; norm_num
-- Equal costs recover `1/2`.
example (c : ℝ) (hc : 0 < c) : sonFraction c c (1 / 2) = 1 / 2 := by
  rw [sonFraction_half hc hc]; field_simp; ring

-- Numerical non-vacuity: in a female-biased population (`y = 1/4`) a son-biased mutant wins,
-- and in a male-biased one (`y = 3/4`) a daughter-biased mutant wins.
example : W (1 / 4) (1 / 4) < W (3 / 4) (1 / 4) := by norm_num [W]
example : W (3 / 4) (3 / 4) < W (1 / 4) (3 / 4) := by norm_num [W]

-- The ESS inequality at the extreme invader fraction `ε = 1` and a mutant near the boundary.
example : W (1 / 100) ((1 - 1) * (1 / 2) + 1 * (1 / 100)) <
    W (1 / 2) ((1 - 1) * (1 / 2) + 1 * (1 / 100)) :=
  W_lt_W_half (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl

#print axioms W_half_right
#print axioms W_lt_W_half
#print axioms forall_W_le_iff
#print axioms hasDerivAt_W_left
#print axioms sonFraction_half

end MathlibExtTest.Biology.PopulationGenetics.Classical.SexRatio
