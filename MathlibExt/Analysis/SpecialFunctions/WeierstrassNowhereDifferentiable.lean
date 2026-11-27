/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.CosineOscillation
public import MathlibExt.Analysis.SpecialFunctions.WeierstrassFunction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The Weierstrass function is nowhere differentiable

The Weierstrass function `W(x) = ∑ₖ cos(160ᵏ x) / 4ᵏ` (see
`WeierstrassFunction.lean`) is differentiable at no point of `ℝ`. The proof
is the classical slope blow-up argument: at any `c`, cosine oscillation
produces points `y` arbitrarily close to `c` whose difference quotients
are arbitrarily large, contradicting the convergence of the slope to a
finite derivative.

## Main results

* `Real.reverse_triangle_three`: `|a + b + c| ≥ |a| - |b| - |c|`.
* `Real.weierstrassFun_slope_lower_bound`: the slope blow-up lemma.
* `Real.weierstrassFun_nowhere_differentiable`: `W` is differentiable
  at no point of `ℝ`.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Weierstrass),
"Section on Derivative (Weierstrass nowhere differentiable function)",
and `v1/Atlas/RealAnalysis/code/Derivatives/Weierstrass.lean`
(`reverse_triangle_three`, `weierstrass_slope_lower_bound`,
`weierstrass_nowhere_differentiable`). The cosine-oscillation input to
the slope lemma is Theorem I of the same v1 file, available as
`Real.exists_cos_oscillation` in `CosineOscillation.lean`.
-/

@[expose] public section

namespace Real

/-- **Reverse triangle inequality, three terms.** For all real numbers
`a`, `b`, `c`, the absolute value of their sum is at least
`|a| - |b| - |c|`. -/
theorem reverse_triangle_three (a b c : ℝ) : |a + b + c| ≥ |a| - |b| - |c| := by
  have h1 : |a| - |b + c| ≤ |a + (b + c)| := abs_sub_abs_le_abs_add a (b + c)
  have h2 : |b + c| ≤ |b| + |c| := abs_add_le b c
  have h3 : a + (b + c) = a + b + c := by ring
  rw [h3] at h1
  linarith

/-- **Slope blow-up lemma.** For every real `c` and every natural number
`n`, there exists a point `y ≠ c` with `|y - c| < 3π / 160ⁿ` such that
the difference quotient of the Weierstrass function between `y` and `c`
has absolute value at least `40ⁿ / (117 π)`. Since
`40ⁿ / (117 π) → ∞`, this witnesses that the function cannot have a
finite derivative at `c`. -/
theorem weierstrassFun_slope_lower_bound (c : ℝ) (n : ℕ) :
    ∃ y : ℝ, y ≠ c ∧ |y - c| < 3 * π / (160 : ℝ) ^ n ∧
      |(weierstrassFun y - weierstrassFun c) / (y - c)| ≥
        (40 : ℝ) ^ n / (117 * π) := by
  have hK : (0 : ℕ) < 160 ^ n := by positivity
  obtain ⟨y, hylb, hyub, hcos_osc⟩ := Real.exists_cos_oscillation c (160 ^ n) hK
  push_cast at hylb hyub hcos_osc
  have hpi_pos : (0 : ℝ) < π := pi_pos
  have h160n_pos : (0 : ℝ) < (160 : ℝ) ^ n := by positivity
  have hymc_pos : 0 < y - c := by linarith [div_pos hpi_pos h160n_pos]
  have hymc_ub : y - c < 3 * π / (160 : ℝ) ^ n := by linarith
  have hyne : y ≠ c := ne_of_gt (by linarith : c < y)
  have habs_yc : |y - c| = y - c := abs_of_pos hymc_pos
  refine ⟨y, hyne, by rw [habs_yc]; exact hymc_ub, ?_⟩
  rw [abs_div, habs_yc]
  rw [ge_iff_le, le_div_iff₀ hymc_pos]
  suffices hsuff : |weierstrassFun y - weierstrassFun c| ≥ 1 / (39 * (4 : ℝ) ^ n) by
    have hcalc : (40 : ℝ) ^ n / (117 * π) * (y - c)
        < (40 : ℝ) ^ n / (117 * π) * (3 * π / (160 : ℝ) ^ n) := by
      apply mul_lt_mul_of_pos_left hymc_ub
      exact div_pos (by positivity) (by linarith [pi_pos])
    have heq : (40 : ℝ) ^ n / (117 * π) * (3 * π / (160 : ℝ) ^ n) =
        1 / (39 * (4 : ℝ) ^ n) := by
      rw [show (160 : ℝ) ^ n = (40 : ℝ) ^ n * (4 : ℝ) ^ n from by
        rw [show (160 : ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
      field_simp; ring
    linarith [heq ▸ hcalc]
  set diff := fun k : ℕ => (cos ((160 : ℝ) ^ k * y) - cos ((160 : ℝ) ^ k * c)) / (4 : ℝ) ^ k
  have hdiff_summable : Summable diff := by
    rw [show diff = (fun k => cos (160 ^ k * y) / (4 : ℝ) ^ k -
        cos (160 ^ k * c) / (4 : ℝ) ^ k) from by
      ext k; simp [diff]; ring]
    exact (summable_weierstrassFun_terms y).sub (summable_weierstrassFun_terms c)
  have hdiff_eq : weierstrassFun y - weierstrassFun c = ∑' k, diff k := by
    simp only [weierstrassFun]
    rw [← (summable_weierstrassFun_terms y).hasSum.sub
      (summable_weierstrassFun_terms c).hasSum |>.tsum_eq]
    congr 1; ext k; simp [diff]; ring
  have hsplit : ∑' k, diff k = (∑ k ∈ Finset.range n, diff k) + diff n +
      ∑' k, diff (k + (n + 1)) := by
    have htail : Summable (fun k => diff (k + (n + 1))) :=
      hdiff_summable.comp_injective (fun a b h => by omega)
    have hkey := (hasSum_nat_add_iff (n + 1)).mp htail.hasSum
    have huniq := hdiff_summable.hasSum.unique hkey
    rw [Finset.sum_range_succ] at huniq; linarith
  have ha : |diff n| ≥ 1 / (4 : ℝ) ^ n := by
    simp only [diff, abs_div, abs_of_pos (show (0 : ℝ) < (4 : ℝ) ^ n by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n)
    rw [abs_sub_comm]; exact hcos_osc
  have hb : |∑ k ∈ Finset.range n, diff k| ≤ 4 / (13 * (4 : ℝ) ^ n) := by
    calc |∑ k ∈ Finset.range n, diff k|
        ≤ ∑ k ∈ Finset.range n, |diff k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, (y - c) * (40 : ℝ) ^ k := by
          apply Finset.sum_le_sum; intro k _
          simp only [diff, abs_div, abs_of_pos (show (0 : ℝ) < (4 : ℝ) ^ k by positivity)]
          calc |cos ((160 : ℝ) ^ k * y) - cos ((160 : ℝ) ^ k * c)| / (4 : ℝ) ^ k
              ≤ ((160 : ℝ) ^ k * (y - c)) / (4 : ℝ) ^ k := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                calc |cos ((160 : ℝ) ^ k * y) - cos ((160 : ℝ) ^ k * c)|
                    ≤ |(160 : ℝ) ^ k * y - (160 : ℝ) ^ k * c| := abs_cos_sub_cos_le _ _
                  _ = (160 : ℝ) ^ k * (y - c) := by
                      rw [show (160 : ℝ) ^ k * y - (160 : ℝ) ^ k * c =
                        (160 : ℝ) ^ k * (y - c) from by ring]
                      exact abs_of_pos (mul_pos (by positivity) hymc_pos)
            _ = (y - c) * (40 : ℝ) ^ k := by
                rw [show (160 : ℝ) ^ k = (40 : ℝ) ^ k * (4 : ℝ) ^ k from by
                  rw [show (160 : ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
                have h4k : (4 : ℝ) ^ k ≠ 0 := by positivity
                field_simp
      _ = (y - c) * ∑ k ∈ Finset.range n, (40 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ (3 * π / (160 : ℝ) ^ n) * ((40 : ℝ) ^ n / 39) := by
          apply mul_le_mul (le_of_lt hymc_ub) _
            (Finset.sum_nonneg fun k _ => by positivity) (by linarith [pi_pos])
          have hgeom := geom_sum_eq (show (40 : ℝ) ≠ 1 from by norm_num) n
          linarith [show (0 : ℝ) < (40 : ℝ) ^ n from by positivity]
      _ = 3 * π / (39 * (4 : ℝ) ^ n) := by
          rw [show (160 : ℝ) ^ n = (40 : ℝ) ^ n * (4 : ℝ) ^ n from by
            rw [show (160 : ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
          field_simp
      _ ≤ 4 / (13 * (4 : ℝ) ^ n) := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 39 * (4 : ℝ) ^ n)
            (by positivity : (0 : ℝ) < 13 * (4 : ℝ) ^ n)]
          nlinarith [pi_lt_four, show (0 : ℝ) < (4 : ℝ) ^ n from by positivity]
  have hc : |∑' k, diff (k + (n + 1))| ≤ 2 / (3 * (4 : ℝ) ^ n) := by
    have htail_summable : Summable (fun k => diff (k + (n + 1))) :=
      hdiff_summable.comp_injective (fun a b h => by omega)
    have hterm_le : ∀ k, |diff (k + (n + 1))| ≤ 2 / (4 : ℝ) ^ (k + (n + 1)) := by
      intro k
      simp only [diff, abs_div,
        abs_of_pos (show (0 : ℝ) < (4 : ℝ) ^ (k + (n + 1)) by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ (k + (n + 1)))
      exact (abs_sub _ _).trans (by
        linarith [abs_cos_le_one (160 ^ (k + (n + 1)) * y),
          abs_cos_le_one (160 ^ (k + (n + 1)) * c)])
    have hsumm2 : Summable (fun k : ℕ => 2 / (4 : ℝ) ^ (k + (n + 1))) := by
      have heq2 : (fun k : ℕ => 2 / (4 : ℝ) ^ (k + (n + 1))) =
          (fun k => (2 / (4 : ℝ) ^ (n + 1)) * ((4 : ℝ)⁻¹) ^ k) := by
        ext k; rw [pow_add]; have h1 : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
        have h2 : (4 : ℝ) ^ k ≠ 0 := by positivity
        rw [show (4 : ℝ)⁻¹ ^ k = 1 / (4 : ℝ) ^ k from by rw [inv_pow, one_div]]; field_simp
      rw [heq2]; exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
    have htail_norm : Summable (fun k => ‖diff (k + (n + 1))‖) := by
      apply Summable.of_norm_bounded (g := fun k => 2 / (4 : ℝ) ^ (k + (n + 1))) hsumm2
      intro k
      rw [norm_norm, Real.norm_eq_abs]
      exact hterm_le k
    calc |∑' k, diff (k + (n + 1))|
        ≤ ∑' k, |diff (k + (n + 1))| := by
          exact le_of_eq_of_le (Real.norm_eq_abs _).symm
            (norm_tsum_le_tsum_norm htail_norm)
      _ ≤ ∑' k : ℕ, 2 / (4 : ℝ) ^ (k + (n + 1)) := by
          apply Summable.tsum_mono htail_norm hsumm2
          intro k; exact hterm_le k
      _ = 2 / (3 * (4 : ℝ) ^ n) := by
          have heq3 : ∀ k, 2 / (4 : ℝ) ^ (k + (n + 1)) =
              (2 / (4 : ℝ) ^ (n + 1)) * ((4 : ℝ)⁻¹) ^ k := by
            intro k; rw [pow_add]; have h1 : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
            have h2 : (4 : ℝ) ^ k ≠ 0 := by positivity
            rw [show (4 : ℝ)⁻¹ ^ k = 1 / (4 : ℝ) ^ k from by rw [inv_pow, one_div]]; field_simp
          simp_rw [heq3]
          rw [tsum_mul_left,
            tsum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹) (by norm_num)]
          rw [show (1 : ℝ) - (4 : ℝ)⁻¹ = 3 / 4 from by norm_num,
            show (3 / 4 : ℝ)⁻¹ = 4 / 3 from by norm_num]
          rw [show (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n from by ring]; ring
  rw [hdiff_eq, hsplit]
  have hrt := reverse_triangle_three (diff n) (∑ k ∈ Finset.range n, diff k)
    (∑' k, diff (k + (n + 1)))
  have hrearrange : ∑ k ∈ Finset.range n, diff k + diff n + ∑' k, diff (k + (n + 1)) =
      diff n + (∑ k ∈ Finset.range n, diff k) + ∑' k, diff (k + (n + 1)) := by ring
  rw [hrearrange]
  linarith [show (1 : ℝ) / (4 : ℝ) ^ n - 4 / (13 * (4 : ℝ) ^ n) - 2 / (3 * (4 : ℝ) ^ n) =
    1 / (39 * (4 : ℝ) ^ n) from by field_simp; ring]

open Filter Topology in
/-- **The Weierstrass function is nowhere differentiable.** The Weierstrass function
$W(x) = \sum_{k=0}^{\infty} \cos(160^k x) / 4^k$ is differentiable at no point of $\mathbb{R}$:
for every real number $c$, $W$ is not differentiable at $c$.

The proof uses the slope blow-up lemma to exhibit a sequence of points approaching $c$ along
which the absolute values of the difference quotients of $W$ tend to infinity, contradicting
the convergence of the slope to a finite derivative. -/
theorem weierstrassFun_nowhere_differentiable :
    ∀ c : ℝ, ¬ DifferentiableAt ℝ weierstrassFun c := by
  intro c hdiff
  have hslope : Filter.Tendsto (slope weierstrassFun c) (𝓝[≠] c)
      (𝓝 (deriv weierstrassFun c)) :=
    hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt
  choose x hxne hxclose hxlarge using fun n => weierstrassFun_slope_lower_bound c n
  have hxc : Filter.Tendsto x Filter.atTop (𝓝 c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htend : Filter.Tendsto (fun n : ℕ => 3 * π / (160 : ℝ) ^ n)
        Filter.atTop (𝓝 0) := by
      have : (fun n : ℕ => 3 * π / (160 : ℝ) ^ n) = (fun n => (3 * π) * (1 / 160) ^ n) := by
        ext n; simp [div_eq_mul_inv, inv_pow]
      rw [this, show (0 : ℝ) = (3 * π) * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds hε)).exists
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      calc |x n - c| < 3 * π / (160 : ℝ) ^ n := hxclose n
        _ ≤ 3 * π / (160 : ℝ) ^ N := by
            apply div_le_div_of_nonneg_left (by linarith [pi_pos]) (by positivity)
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 160) hn
        _ < ε := hN⟩
  have hslope_seq : Filter.Tendsto (fun n => slope weierstrassFun c (x n)) Filter.atTop
      (𝓝 (deriv weierstrassFun c)) := by
    apply hslope.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hxc
      (Filter.Eventually.of_forall fun n => hxne n)
  have hslope_norm : Filter.Tendsto (fun n => ‖slope weierstrassFun c (x n)‖)
      Filter.atTop (𝓝 ‖deriv weierstrassFun c‖) := hslope_seq.norm
  have hslope_eq : ∀ n, slope weierstrassFun c (x n) =
      (weierstrassFun (x n) - weierstrassFun c) / (x n - c) := by
    intro n; simp [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
  have habs_large : ∀ n, ‖slope weierstrassFun c (x n)‖ ≥
      (40 : ℝ) ^ n / (117 * π) := by
    intro n
    rw [Real.norm_eq_abs, hslope_eq]
    exact hxlarge n
  have h40_tendsto : Filter.Tendsto (fun n : ℕ => (40 : ℝ) ^ n / (117 * π))
      Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_div_const (by linarith [pi_pos] : (0 : ℝ) < 117 * π)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 40)
  have habs_tendsto : Filter.Tendsto (fun n => ‖slope weierstrassFun c (x n)‖)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => habs_large n) h40_tendsto
  exact not_tendsto_atTop_of_tendsto_nhds hslope_norm habs_tendsto

end Real
