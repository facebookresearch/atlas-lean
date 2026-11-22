/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Weierstrass function

The Weierstrass function `W(x) = ∑ₖ cos(160ᵏ x) / 4ᵏ` is the classical
example of a function that is continuous everywhere but differentiable
nowhere on `ℝ`. This file introduces the function and proves the
well-behavedness of its defining series (Theorem III in the book): the
series converges absolutely at every point, the function is continuous,
and it is bounded by `4 / 3`. Nowhere differentiability is proved in
`WeierstrassNowhereDifferentiable.lean`.

Mathlib has no Weierstrass function: it has the Lipschitz estimate
`Real.abs_cos_sub_cos_le` and the Weierstrass approximation theorem via
Stone–Weierstrass, but no continuous nowhere-differentiable function.

## Main results

* `Real.weierstrassFun`: the Weierstrass function.
* `Real.summable_weierstrassFun_terms`: the defining series is summable.
* `Real.summable_abs_weierstrassFun_terms`: the defining series converges
  absolutely.
* `Real.continuous_weierstrassFun`: the Weierstrass function is continuous.
* `Real.weierstrassFun_abs_le`: `|W(x)| ≤ 4 / 3` for all `x`.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem III, "Section on
Derivative (Weierstrass nowhere differentiable function)", and
`v1/Atlas/RealAnalysis/code/Derivatives/Weierstrass.lean`
(`weierstrass_fun`, `weierstrass_theorem_III`, `weierstrass_summable`).
-/

@[expose] public section

namespace Real

/-- The **Weierstrass function** `W(x) = ∑ₖ cos(160ᵏ x) / 4ᵏ`, defined as
a `tsum` over the natural numbers. -/
noncomputable def weierstrassFun (x : ℝ) : ℝ :=
  ∑' k : ℕ, cos (160 ^ k * x) / 4 ^ k

/-- Each term of the Weierstrass series is bounded in norm by the
corresponding term `(1 / 4)ᵏ` of a convergent geometric series. -/
theorem norm_weierstrassFun_term_le (k : ℕ) (x : ℝ) :
    ‖cos (160 ^ k * x) / 4 ^ k‖ ≤ (1 / 4 : ℝ) ^ k := by
  have h4pos : (0 : ℝ) < 4 ^ k := by positivity
  rw [norm_div]
  have h_norm_4k : ‖(4 : ℝ) ^ k‖ = 4 ^ k := by
    rw [Real.norm_eq_abs]; exact abs_of_pos h4pos
  rw [h_norm_4k]
  have h_cos_le : ‖cos (160 ^ k * x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  calc ‖cos (160 ^ k * x)‖ / 4 ^ k
      ≤ 1 / 4 ^ k := div_le_div_of_nonneg_right h_cos_le (le_of_lt h4pos)
    _ = (1 / 4) ^ k := by rw [one_div, one_div, ← inv_pow]

/-- The defining series of the Weierstrass function is summable at every
point, by comparison with the geometric series `∑ (1 / 4)ᵏ`. -/
theorem summable_weierstrassFun_terms (x : ℝ) :
    Summable (fun k : ℕ => cos (160 ^ k * x) / (4 : ℝ) ^ k) := by
  apply Summable.of_norm_bounded (g := fun k => (1 / 4 : ℝ) ^ k)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro k
    exact norm_weierstrassFun_term_le k x

/-- **Theorem III (1).** The defining series of the Weierstrass function is
absolutely convergent at every point. -/
theorem summable_abs_weierstrassFun_terms (x : ℝ) :
    Summable (fun k : ℕ => |cos (160 ^ k * x) / 4 ^ k|) := by
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => by
      have h := norm_weierstrassFun_term_le k x
      rwa [Real.norm_eq_abs] at h)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num))

/-- **Theorem III (2).** The Weierstrass function is continuous on `ℝ`
(it is a uniform limit of continuous partial sums). -/
theorem continuous_weierstrassFun : Continuous weierstrassFun := by
  unfold weierstrassFun
  exact continuous_tsum (u := fun k => (1 / 4 : ℝ) ^ k)
    (fun k => (continuous_cos.comp (continuous_const.mul continuous_id)).div_const _)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun k x => norm_weierstrassFun_term_le k x)

/-- **Theorem III (3).** The Weierstrass function is bounded: `|W(x)| ≤ 4 / 3`
for all `x`. -/
theorem weierstrassFun_abs_le (x : ℝ) : |weierstrassFun x| ≤ 4 / 3 := by
  unfold weierstrassFun
  rw [show |∑' k, cos (160 ^ k * x) / 4 ^ k| = ‖∑' k, cos (160 ^ k * x) / 4 ^ k‖ from
    (Real.norm_eq_abs _).symm]
  have hnorm_summ : Summable (fun k : ℕ => ‖cos (160 ^ k * x) / 4 ^ k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_weierstrassFun_term_le k x)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  calc ‖∑' k, cos (160 ^ k * x) / 4 ^ k‖
      ≤ ∑' k, ‖cos (160 ^ k * x) / 4 ^ k‖ :=
        norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ k :=
        Summable.tsum_mono hnorm_summ
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))
          (fun k => norm_weierstrassFun_term_le k x)
    _ = (1 - 1 / 4)⁻¹ := tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = 4 / 3 := by norm_num

end Real
