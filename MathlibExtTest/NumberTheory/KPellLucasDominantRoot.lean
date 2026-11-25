/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.GeomSum
import MathlibExt.NumberTheory.KPellLucasDominantRoot

/-! # Boundary test for the generalized Pell–Lucas dominant-root estimate -/

namespace MathlibExtTest.KPellLucasDominantRoot

open Real

-- The hypotheses have a witness at the smallest allowed order and at index zero.
example : ∃ α : ℝ, 2 ≤ α ∧ α ≤ 3 ∧
    α ^ 50 = 2 * α ^ 49 + ∑ i ∈ Finset.range 49, α ^ i ∧
    ∃ ξ : ℝ, (2 * α - 2) * ((α - 1) / (51 * α ^ 2 - 150 * α + 50 - 1)) =
        2 * goldenRatio / (goldenRatio + 2) * (1 + ξ) ∧
      |ξ| < 1.25 / goldenRatio ^ (25 : ℝ) := by
  let p (x : ℝ) := x ^ 50 - 2 * x ^ 49 - ∑ i ∈ Finset.range 49, x ^ i
  have hp : Continuous p := by unfold p; fun_prop
  have htwo : p 2 ≤ 0 := by
    dsimp only [p]
    rw [show (2 : ℝ) ^ 50 = 2 * 2 ^ 49 from pow_succ' 2 49, sub_self, zero_sub, neg_nonpos]
    positivity
  have hthree : 0 ≤ p 3 := by
    dsimp only [p]
    rw [show (3 : ℝ) ^ 50 = 3 * 3 ^ 49 from pow_succ' 3 49]
    have hgeom := geom_sum_mul (3 : ℝ) 49
    have hpow : (1 : ℝ) ≤ 3 ^ (49 : ℕ) := one_le_pow₀ (by norm_num)
    linarith only [hgeom, hpow]
  obtain ⟨α, hα, hpα⟩ := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3)
    hp.continuousOn (show 0 ∈ Set.Icc (p 2) (p 3) from ⟨htwo, hthree⟩)
  have hroot : α ^ 50 = 2 * α ^ 49 + ∑ i ∈ Finset.range 49, α ^ i := by
    dsimp only [p] at hpα
    linarith only [hpα]
  have hindex : (0 : ℝ) < goldenRatio ^ ((50 : ℝ) / 2) := by positivity
  refine ⟨α, hα.1, hα.2, hroot, ?_⟩
  have hmain := MetaMathlibExt.kPellLucas_dominantRoot_main_term 50 0 (hk := le_rfl)
    (hnk := by simpa using hindex) α (lt_of_lt_of_le (by norm_num) hα.1) (hroot := hroot)
  norm_num at hmain ⊢
  exact hmain

end MathlibExtTest.KPellLucasDominantRoot
