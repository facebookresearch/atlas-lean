/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SubExponential
public import Mathlib.Probability.Distributions.Gaussian.Real
import MathlibExt.Probability.Distributions.ChiSquare

/-!
# Bernstein's condition and the `χ²` tail bound

Following Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge
University Press, 2019), §2.1.3, this file proves:

* `mgf_le_of_bernsteinCondition`: **Bernstein's moment generating function bound**. If `X` is
  centred, has all moments, has variance `σ² = E[X²]` and satisfies the Bernstein condition
  `|E[X^k]| ≤ k! σ² b^(k-2) / 2` for `k ≥ 3`, with `b ≥ 0`, then for `b |t| < 1` the function
  `exp (t X)` is integrable and `E[exp (t X)] ≤ exp (t² σ² / (2 (1 - b |t|)))`.
* `measureReal_abs_ge_le_of_bernsteinCondition`: **Bernstein's inequality** under the same
  hypotheses, `P(|X| ≥ t) ≤ 2 exp (-t² / (2 (σ² + b t)))` for `t ≥ 0`.
* `hasSubexponentialMGF_sq_sub_one_gaussianReal`: if `Z` is standard normal, then `Z² - 1` is
  sub-exponential with parameters `(2, 4)`.
* `measureReal_abs_chiSq_mean_sub_one_ge_le`: the **`χ²_n` tail bound**
  `P(|(1/n) ∑ Zₖ² - 1| ≥ t) ≤ 2 exp (-n t² / 8)` for independent standard normal `Zₖ` and
  `0 < t < 1`.

They complement `MathlibExt.Probability.SubExponential`, which proves the sub-exponential tail
bounds, the sub-exponential parameters of sums of independent variables and Bernstein's inequality
for bounded variables.

## Proof outline

* Bernstein's moment generating function bound. The hypotheses bound only `|E[X^k]|`, which is
  `E|X|^k` for even `k`. For odd `k = 2j + 3`, the pointwise inequality
  `|x|^(2j+3) ≤ (a x^(2j+2) + x^(2j+4) / a) / 2`, from `(|x| - a)² ≥ 0`, with `a = (2j + 3) b`
  bounds `E|X|^k` by the two neighbouring even moments, and gives `E|X|^k ≤ k! σ² b^(k-2)` for
  every `k ≥ 2`. Hence `∑ E|t X|^k / k!` converges when `b |t| < 1`: its sum is the integral of
  `exp |t X|`, which is therefore integrable, and it justifies the termwise integration
  `E[exp (t X)] = ∑ t^k E[X^k] / k!`. The terms `k ≤ 2` sum to `1 + t² σ² / 2`, the Bernstein
  condition bounds the others by a geometric series, and
  `1 + t² σ² / (2 (1 - b |t|)) ≤ exp (t² σ² / (2 (1 - b |t|)))`. When `b = 0` the condition gives
  `E[X⁴] = 0`, so `X = 0` almost surely.
* Bernstein's inequality. The Chernoff bound at `±t / (σ² + b t)` on each tail, as for bounded
  variables; when `σ = 0`, `X = 0` almost surely.
* The centred `χ²₁` variable. The Gaussian integral `E[exp (t Z²)] = 1 / √(1 - 2t)` of
  `ProbabilityTheory.mgf_sq_stdGaussian` gives `E[exp (t (Z² - 1))] = e^{-t} / √(1 - 2t)`, which is
  positive for `t < 1/2`. For `|t| < 1/4`, squaring reduces `e^{-t} / √(1 - 2t) ≤ exp (2 t²)` to
  `1 ≤ (1 - u) exp (u + u²)` with `u = 2t`, which follows from `exp y ≥ 1 + y` when `u ≤ 0`, and
  from `exp u ≥ 1 + u + u²/2 + u³/6` and `exp (u²) ≥ 1 + u²` when `0 ≤ u ≤ 1/2`.
* The `χ²_n` tail. The coordinates are independent under the product measure, so the sum `S` of
  the `n` variables `Zₖ² - 1` is sub-exponential with parameters `(2 √n, 4)`, and the
  Gaussian-regime tail bound at `n t ≤ (2 √n)² / 4`, applied to `S` and `-S`, gives
  `2 exp (-(n t)² / (8 n))`. When `n = 0` the right-hand side is `2`.

## Implementation notes

The four theorems keep the full names, statements and docstrings they had in the wanted module
`WantedExt.Probability.HighDimensionalStatisticsWanted`, so their namespace still reads
`HighDimensionalStatisticsWanted`.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
  Press, 2019, §2.1.3.
* "Rinaldo 2017" is A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3 (Carnegie Mellon,
  2017), an open account of the same statements with the same constants, except that its
  Example 3.8 omits the factor `2` of the two-sided `χ²_n` tail bound.
-/

namespace MathlibExt.Probability.HighDimensionalStatisticsWanted

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ### Bernstein's condition -/

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {b σ : ℝ}

/-- For `a > 0`, `|x|^(2j+3) ≤ (a x^(2j+2) + x^(2j+4) / a) / 2`. -/
private lemma abs_pow_odd_le (x : ℝ) {a : ℝ} (ha : 0 < a) (j : ℕ) :
    |x| ^ (2 * j + 3) ≤ (a * x ^ (2 * j + 2) + x ^ (2 * j + 4) / a) / 2 := by
  have h2 : x ^ (2 * j + 2) = |x| ^ (2 * j + 2) := (Even.pow_abs ⟨j + 1, by ring⟩ x).symm
  have h4 : x ^ (2 * j + 4) = |x| ^ (2 * j + 4) := (Even.pow_abs ⟨j + 2, by ring⟩ x).symm
  rw [h2, h4]
  have key : (a * |x| ^ (2 * j + 2) + |x| ^ (2 * j + 4) / a) / 2 - |x| ^ (2 * j + 3) =
      |x| ^ (2 * j + 2) * (|x| - a) ^ 2 / (2 * a) := by
    field_simp
    ring
  have : 0 ≤ |x| ^ (2 * j + 2) * (|x| - a) ^ 2 / (2 * a) := by positivity
  linarith

/-- The Bernstein condition extended to `k = 2`, where the variance gives equality. -/
private lemma abs_integral_pow_le
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    (k : ℕ) :
    |∫ ω, X ω ^ (k + 2) ∂μ| ≤ (k + 2).factorial * σ ^ 2 * b ^ k / 2 := by
  rcases k with _ | k
  · simp [hvar, Nat.factorial]
  · simpa using hbern (k + 1 + 2) (by omega)

/-- Absolute moments under the Bernstein condition: `E|X|^k ≤ k! σ² b^(k-2)` for `k ≥ 2`. -/
private lemma integral_abs_pow_le (hb : 0 < b) (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ)
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    (k : ℕ) :
    ∫ ω, |X ω| ^ (k + 2) ∂μ ≤ (k + 2).factorial * σ ^ 2 * b ^ k := by
  have hσ : 0 ≤ σ ^ 2 := sq_nonneg σ
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · -- The even exponent `2j + 2`.
    have he : (fun ω ↦ |X ω| ^ (2 * j + 2)) = fun ω ↦ X ω ^ (2 * j + 2) := by
      funext ω
      exact Even.pow_abs ⟨j + 1, by ring⟩ _
    rw [he]
    have h := (le_abs_self _).trans (abs_integral_pow_le hvar hbern (2 * j))
    have : 0 ≤ ((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j) := by positivity
    linarith
  · -- The odd exponent `2j + 3`, between the even exponents `2j + 2` and `2j + 4`.
    set a : ℝ := (2 * j + 3) * b with ha_def
    have ha : 0 < a := by positivity
    have hpt : ∀ ω, |X ω| ^ (2 * j + 1 + 2) ≤
        (a * X ω ^ (2 * j + 2) + X ω ^ (2 * j + 4) / a) / 2 := fun ω ↦ by
      simpa using abs_pow_odd_le (X ω) ha j
    have hI2 := hint (2 * j + 2)
    have hI4 := hint (2 * j + 4)
    have hle : ∫ ω, |X ω| ^ (2 * j + 1 + 2) ∂μ ≤
        ∫ ω, (a * X ω ^ (2 * j + 2) + X ω ^ (2 * j + 4) / a) / 2 ∂μ :=
      integral_mono (by simpa using (hint (2 * j + 3)).abs)
        (((hI2.const_mul a).add (hI4.div_const a)).div_const 2) hpt
    have hcomp : ∫ ω, (a * X ω ^ (2 * j + 2) + X ω ^ (2 * j + 4) / a) / 2 ∂μ =
        (a * ∫ ω, X ω ^ (2 * j + 2) ∂μ + (∫ ω, X ω ^ (2 * j + 4) ∂μ) / a) / 2 := by
      rw [integral_div, integral_add (hI2.const_mul a) (hI4.div_const a), integral_const_mul,
        integral_div]
    rw [hcomp] at hle
    have h2 := (le_abs_self _).trans (abs_integral_pow_le hvar hbern (2 * j))
    have h4 := (le_abs_self _).trans (abs_integral_pow_le hvar hbern (2 * j + 2))
    refine hle.trans ?_
    have hf3 : ((2 * j + 3).factorial : ℝ) = (2 * j + 3) * (2 * j + 2).factorial := by
      rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    have hf4 : ((2 * j + 2 + 2).factorial : ℝ) =
        (2 * j + 4) * (2 * j + 3) * (2 * j + 2).factorial := by
      rw [show 2 * j + 2 + 2 = (2 * j + 2) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    rw [show 2 * j + 1 + 2 = 2 * j + 3 by ring, hf3]
    rw [hf4] at h4
    have hF : (0 : ℝ) < (2 * j + 2).factorial := by positivity
    rw [show 2 * j + 2 + 2 = 2 * j + 4 by ring] at h4
    have hA : a * ∫ ω, X ω ^ (2 * j + 2) ∂μ ≤
        a * (((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j) / 2) :=
      mul_le_mul_of_nonneg_left h2 ha.le
    have hB : (∫ ω, X ω ^ (2 * j + 4) ∂μ) / a ≤
        ((2 * j + 4) * (2 * j + 3) * ((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j + 2) / 2) /
          a := by
      gcongr
    have hfin : (a * (((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j) / 2) +
        ((2 * j + 4) * (2 * j + 3) * ((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j + 2) / 2) /
          a) / 2 ≤
        (2 * j + 3) * ((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j + 1) := by
      rw [ha_def]
      have hb' : b ^ (2 * j + 1) = b ^ (2 * j) * b := pow_succ _ _
      have hb'' : b ^ (2 * j + 2) = b ^ (2 * j) * b * b := by ring
      rw [hb', hb'']
      have hpos : 0 ≤ ((2 * j + 2).factorial : ℝ) * σ ^ 2 * b ^ (2 * j) * b := by positivity
      field_simp
      nlinarith [hpos]
    linarith

/-- Under the Bernstein condition with `b > 0` and `b |t| < 1`, the series of absolute moments
`∑ E|t X|^k / k!` converges. -/
private lemma summable_integral_abs_pow (hb : 0 < b)
    (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    {t : ℝ} (ht : b * |t| < 1) :
    Summable fun k : ℕ ↦ ∫ ω, |t * X ω| ^ k / k.factorial ∂μ := by
  rw [← summable_nat_add_iff 2]
  have hg : Summable fun k : ℕ ↦ σ ^ 2 * t ^ 2 * (b * |t|) ^ k :=
    (summable_geometric_of_lt_one (by positivity) ht).mul_left _
  refine hg.of_nonneg_of_le (fun k ↦ integral_nonneg fun ω ↦ by positivity) fun k ↦ ?_
  have hcalc : ∫ ω, |t * X ω| ^ (k + 2) / ((k + 2).factorial : ℝ) ∂μ =
      |t| ^ (k + 2) / (k + 2).factorial * ∫ ω, |X ω| ^ (k + 2) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [abs_mul, mul_pow]
    ring
  rw [hcalc]
  have hF : (0 : ℝ) < (k + 2).factorial := by positivity
  calc |t| ^ (k + 2) / (k + 2).factorial * ∫ ω, |X ω| ^ (k + 2) ∂μ
      ≤ |t| ^ (k + 2) / (k + 2).factorial * ((k + 2).factorial * σ ^ 2 * b ^ k) :=
        mul_le_mul_of_nonneg_left (integral_abs_pow_le hb hint hvar hbern k) (by positivity)
    _ = σ ^ 2 * t ^ 2 * (b * |t|) ^ k := by
        rw [← sq_abs t]
        field_simp
        ring

end Moments

/-- **Bernstein's moment generating function bound** (Wainwright, *High-Dimensional Statistics*,
2019, §2.1.3; Rinaldo 2017, Definition 3.3 and Theorem 3.4). Let `X` be a centred real random
variable with all moments finite and
variance `σ² = E[X²]`, satisfying the Bernstein condition with parameter `b ≥ 0`:
`|E[X^k]| ≤ k! σ² b^(k-2) / 2` for every `k ≥ 3`. Then for every `t` with `b |t| < 1`,
`exp (t X)` is integrable and `E[exp (t X)] ≤ exp (t² σ² / (2 (1 - b |t|)))`. The source states
the condition for `k = 2, 3, …` about the mean `μ`; it holds with equality at `k = 2`. -/
public theorem mgf_le_of_bernsteinCondition {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {b σ : ℝ} (hb : 0 ≤ b)
    (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (hmean : μ[X] = 0)
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    {t : ℝ} (ht : b * |t| < 1) :
    Integrable (fun ω ↦ exp (t * X ω)) μ ∧
      mgf X μ t ≤ exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|))) := by
  have hXm : AEStronglyMeasurable X μ := by simpa using (hint 1).aestronglyMeasurable
  rcases hb.lt_or_eq with hb | rfl
  swap
  · -- The case `b = 0`: the fourth moment vanishes, so `X = 0` almost surely.
    have h4 : ∫ ω, X ω ^ 4 ∂μ = 0 := by
      have h := hbern 4 (by norm_num)
      norm_num at h
      exact h
    have hX0 : ∀ᵐ ω ∂μ, X ω = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun ω ↦ by positivity) (hint 4)).mp h4
      filter_upwards [h] with ω hω
      simpa using hω
    have hexp : (fun ω ↦ exp (t * X ω)) =ᵐ[μ] fun _ ↦ 1 := by
      filter_upwards [hX0] with ω hω
      simp [hω]
    refine ⟨(integrable_const 1).congr hexp.symm, ?_⟩
    rw [mgf, integral_congr_ae hexp]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    exact one_le_exp (by positivity)
  -- The case `b > 0`: expand `exp (t X)` as a power series and integrate termwise.
  set F : ℕ → Ω → ℝ := fun k ω ↦ (t * X ω) ^ k / k.factorial with hF_def
  set G : ℕ → Ω → ℝ := fun k ω ↦ |t * X ω| ^ k / k.factorial with hG_def
  have hFint : ∀ k, Integrable (F k) μ := fun k ↦ by
    simp_rw [hF_def, mul_pow]
    exact ((hint k).const_mul _).div_const _
  have hGint : ∀ k, Integrable (G k) μ := fun k ↦ by
    simp_rw [hG_def, abs_mul, mul_pow, ← abs_pow]
    exact ((hint k).abs.const_mul _).div_const _
  have hsum := summable_integral_abs_pow hb hint hvar hbern ht
  have hFn : (fun k ↦ ∫ ω, ‖F k ω‖ ∂μ) = fun k ↦ ∫ ω, G k ω ∂μ := by
    funext k
    congr 1
    funext ω
    simp [hF_def, hG_def, norm_div, norm_pow, Real.norm_eq_abs]
  have hGn : (fun k ↦ ∫ ω, ‖G k ω‖ ∂μ) = fun k ↦ ∫ ω, G k ω ∂μ := by
    funext k
    congr 1
    funext ω
    exact Real.norm_of_nonneg (by positivity)
  have hexpF : ∀ ω, ∑' k, F k ω = exp (t * X ω) := fun ω ↦ by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hexpG : ∀ ω, ∑' k, G k ω = exp |t * X ω| := fun ω ↦ by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- `exp |t X|` is integrable, since its integral `∑ E|t X|^k / k!` is at least `1`.
  have hGsum := hasSum_integral_of_summable_integral_norm hGint (hGn ▸ hsum)
  simp_rw [hexpG] at hGsum
  have hint_abs : Integrable (fun ω ↦ exp |t * X ω|) μ := by
    refine Integrable.of_integral_ne_zero (ne_of_gt ?_)
    have h0 := le_hasSum hGsum 0 fun k _ ↦ integral_nonneg fun ω ↦ by positivity
    simp only [hG_def, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, integral_const,
      probReal_univ, smul_eq_mul, mul_one] at h0
    linarith
  have hint_t : Integrable (fun ω ↦ exp (t * X ω)) μ :=
    hint_abs.mono' (continuous_exp.comp_aestronglyMeasurable (hXm.const_mul t))
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_of_nonneg (exp_pos _).le]
        exact exp_le_exp.mpr (le_abs_self _))
  refine ⟨hint_t, ?_⟩
  have hmgf := hasSum_integral_of_summable_integral_norm hFint (hFn ▸ hsum)
  simp_rw [hexpF] at hmgf
  -- The terms of the series.
  have hc : ∀ k, ∫ ω, F k ω ∂μ = t ^ k * (∫ ω, X ω ^ k ∂μ) / k.factorial := fun k ↦ by
    simp_rw [hF_def, mul_pow]
    rw [integral_div, integral_const_mul]
  have hden : 0 < 1 - b * |t| := by linarith
  have hg : HasSum (fun k : ℕ ↦ t ^ 2 * σ ^ 2 / 2 * (b * |t|) ^ k)
      (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|))) := by
    have := (hasSum_geometric_of_lt_one (by positivity) ht).mul_left (t ^ 2 * σ ^ 2 / 2)
    convert this using 1
    field_simp
  have htail : ∀ k : ℕ, ∫ ω, F (k + 2) ω ∂μ ≤ t ^ 2 * σ ^ 2 / 2 * (b * |t|) ^ k := fun k ↦ by
    rw [hc]
    have hF : (0 : ℝ) < (k + 2).factorial := by positivity
    calc t ^ (k + 2) * (∫ ω, X ω ^ (k + 2) ∂μ) / (k + 2).factorial
        ≤ |t ^ (k + 2) * (∫ ω, X ω ^ (k + 2) ∂μ) / (k + 2).factorial| := le_abs_self _
      _ = |t| ^ (k + 2) * |∫ ω, X ω ^ (k + 2) ∂μ| / (k + 2).factorial := by
          rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      _ ≤ |t| ^ (k + 2) * ((k + 2).factorial * σ ^ 2 * b ^ k / 2) / (k + 2).factorial := by
          gcongr
          exact abs_integral_pow_le hvar hbern k
      _ = t ^ 2 * σ ^ 2 / 2 * (b * |t|) ^ k := by
          rw [← sq_abs t]
          field_simp
          ring
  have hsplit := (hmgf.summable.sum_add_tsum_nat_add 2).symm
  rw [mgf, ← hmgf.tsum_eq, hsplit]
  have hhead : ∑ i ∈ Finset.range 2, ∫ ω, F i ω ∂μ = 1 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hc]
    simp [hmean]
  rw [hhead]
  have hle := ((summable_nat_add_iff 2).mpr hmgf.summable).tsum_le_tsum htail hg.summable
  rw [hg.tsum_eq] at hle
  linarith [add_one_le_exp (t ^ 2 * σ ^ 2 / (2 * (1 - b * |t|)))]

/-- **Bernstein's inequality under the Bernstein condition** (Wainwright, *High-Dimensional
Statistics*, 2019, §2.1.3; Rinaldo 2017, Theorem 3.5). Under the hypotheses of
`mgf_le_of_bernsteinCondition`, for every `t ≥ 0`,
`P(|X| ≥ t) ≤ 2 exp (-t² / (2 (σ² + b t)))`. -/
public theorem measureReal_abs_ge_le_of_bernsteinCondition {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {b σ : ℝ}
    (hb : 0 ≤ b) (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (hmean : μ[X] = 0)
    (hvar : ∫ ω, X ω ^ 2 ∂μ = σ ^ 2)
    (hbern : ∀ k : ℕ, 3 ≤ k → |∫ ω, X ω ^ k ∂μ| ≤ k.factorial * σ ^ 2 * b ^ (k - 2) / 2)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
  rcases (sq_nonneg σ).lt_or_eq with hσ | hσ
  swap
  · -- The case `σ = 0`: `X = 0` almost surely.
    have hX0 : ∀ᵐ ω ∂μ, X ω = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun ω ↦ by positivity) (hint 2)).mp
        (hvar.trans hσ.symm)
      filter_upwards [h] with ω hω
      simpa using hω
    rcases ht.lt_or_eq with ht | rfl
    · have hnull : μ.real {ω | t ≤ |X ω|} = 0 := by
        rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
        filter_upwards [hX0] with ω hω
        simp [hω, ht]
      rw [hnull]
      positivity
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
        exp_zero, mul_one]
      linarith [measureReal_le_one (μ := μ) (s := {ω | 0 ≤ |X ω|})]
  -- The case `σ > 0`: the Chernoff bound at `s = t / (σ² + b t)`, on both tails.
  have hD : 0 < σ ^ 2 + b * t := by positivity
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set s := t / (σ ^ 2 + b * t) with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hbs : b * |s| < 1 := by
    rw [abs_of_nonneg hs0, hs_def, mul_div_assoc', div_lt_one hD]
    linarith
  have hbs' : b * |-s| < 1 := by rwa [abs_neg]
  have hden : 1 - b * |s| = σ ^ 2 / (σ ^ 2 + b * t) := by
    rw [abs_of_nonneg hs0, hs_def]
    field_simp
    ring
  obtain ⟨hint_s, hmgf_s⟩ := mgf_le_of_bernsteinCondition hb hint hmean hvar hbern hbs
  obtain ⟨hint_ns, hmgf_ns⟩ := mgf_le_of_bernsteinCondition hb hint hmean hvar hbern hbs'
  rw [abs_neg] at hmgf_ns
  have hval : exp (-s * t) * exp (s ^ 2 * σ ^ 2 / (2 * (1 - b * |s|))) =
      exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
    rw [← exp_add, hden, hs_def]
    congr 1
    field_simp
    ring
  have hup : μ.real {ω | t ≤ X ω} ≤ exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
    calc μ.real {ω | t ≤ X ω} ≤ exp (-s * t) * mgf X μ s :=
          measure_ge_le_exp_mul_mgf t hs0 hint_s
      _ ≤ exp (-s * t) * exp (s ^ 2 * σ ^ 2 / (2 * (1 - b * |s|))) := by gcongr
      _ = _ := hval
  have hlow : μ.real {ω | X ω ≤ -t} ≤ exp (-t ^ 2 / (2 * (σ ^ 2 + b * t))) := by
    calc μ.real {ω | X ω ≤ -t} ≤ exp (-(-s) * -t) * mgf X μ (-s) :=
          measure_le_le_exp_mul_mgf (-t) (by linarith) hint_ns
      _ ≤ exp (-(-s) * -t) * exp ((-s) ^ 2 * σ ^ 2 / (2 * (1 - b * |s|))) := by gcongr
      _ = _ := by rw [neg_sq, show -(-s) * -t = -s * t by ring]; exact hval
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; exact h
    · left; exact h
  calc μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | X ω ≤ -t}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-! ### The `χ²` distribution -/

/-- The scalar inequality behind the `χ²₁` bound: `1 ≤ (1 - u) exp (u + u²)` for `|u| ≤ 1/2`. -/
private lemma one_le_one_sub_mul_exp {u : ℝ} (hu : |u| ≤ 1 / 2) :
    1 ≤ (1 - u) * exp (u + u ^ 2) := by
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  rcases le_total u 0 with h | h
  · -- `exp (u + u²) ≥ 1 + u + u²` and `(1 - u) (1 + u + u²) = 1 - u³ ≥ 1`.
    have he := add_one_le_exp (u + u ^ 2)
    nlinarith [mul_le_mul_of_nonneg_left he (by linarith : (0 : ℝ) ≤ 1 - u),
      pow_two_nonneg u, mul_nonneg (neg_nonneg.mpr h) (pow_two_nonneg u)]
  · -- `exp u ≥ 1 + u + u²/2 + u³/6` and `exp u² ≥ 1 + u²`.
    have h1 : 1 + u + u ^ 2 / 2 + u ^ 3 / 6 ≤ exp u := by
      have := Real.sum_le_exp_of_nonneg h 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have h2 : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith [add_one_le_exp (u ^ 2)]
    have hprod : (1 + u + u ^ 2 / 2 + u ^ 3 / 6) * (1 + u ^ 2) ≤ exp (u + u ^ 2) := by
      rw [exp_add]
      exact mul_le_mul h1 h2 (by positivity) (exp_pos _).le
    have hpoly : 1 ≤ (1 - u) * ((1 + u + u ^ 2 / 2 + u ^ 3 / 6) * (1 + u ^ 2)) := by
      nlinarith [pow_two_nonneg u, mul_nonneg h (pow_two_nonneg u),
        mul_nonneg (mul_nonneg h h) (pow_two_nonneg u), pow_nonneg h 4, pow_nonneg h 5]
    exact hpoly.trans (mul_le_mul_of_nonneg_left hprod (by linarith))

/-- The moment generating function of `Z² - 1` for a standard normal `Z`:
`E[exp (t (Z² - 1))] = e^{-t} / √(1 - 2t)`, from `E[exp (t Z²)] = 1 / √(1 - 2t)`. -/
private lemma mgf_sq_sub_one_gaussianReal (t : ℝ) :
    mgf (fun x : ℝ ↦ x ^ 2 - 1) (gaussianReal 0 1) t = exp (-t) / √(1 - 2 * t) := by
  have h := mgf_add_const (X := fun x : ℝ ↦ x ^ 2) (μ := gaussianReal 0 1) (t := t) (-1)
  simp only [← sub_eq_add_neg] at h
  rw [h, mgf_sq_stdGaussian, mul_neg, mul_one, div_eq_mul_inv, mul_comm]

/-- **A centred `χ²₁` variable is sub-exponential with parameters `(2, 4)`** (Wainwright,
*High-Dimensional Statistics*, 2019, §2.1.3, the `χ²` example): if `Z` is standard normal, then
`Z² - 1`
satisfies `E[exp (t (Z² - 1))] ≤ exp (4 t² / 2)` for `|t| < 1 / 4`. Here `Z` is the identity on
`ℝ` under `gaussianReal 0 1`. -/
public theorem hasSubexponentialMGF_sq_sub_one_gaussianReal :
    HasSubexponentialMGF (fun x : ℝ ↦ x ^ 2 - 1) 2 4 (gaussianReal 0 1) := by
  have hbound : ∀ t : ℝ, ((4 : ℝ≥0) : ℝ) * |t| < 1 → |t| < 1 / 4 := fun t ht ↦ by
    push_cast at ht
    linarith
  have hhalf : ∀ t : ℝ, |t| < 1 / 4 → t < 1 / 2 := fun t ht ↦ by
    linarith [le_abs_self t]
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have ht' := hhalf t (hbound t ht)
    rw [← mgf_pos_iff, mgf_sq_sub_one_gaussianReal]
    have : 0 < √(1 - 2 * t) := Real.sqrt_pos.mpr (by linarith)
    positivity
  · have ht4 := hbound t ht
    have ht' := hhalf t ht4
    have h12 : 0 < 1 - 2 * t := by linarith
    have hs : 0 < √(1 - 2 * t) := Real.sqrt_pos.mpr h12
    rw [mgf_sq_sub_one_gaussianReal, div_le_iff₀ hs]
    have hu : |2 * t| ≤ 1 / 2 := by
      rw [abs_mul, abs_two]
      linarith
    have key := one_le_one_sub_mul_exp hu
    -- Square both sides: `e^{-2t} ≤ e^{4t²} (1 - 2t)`.
    refine (pow_le_pow_iff_left₀ (exp_pos _).le (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, Real.sq_sqrt h12.le, ← exp_nat_mul, ← exp_nat_mul]
    have hexp : exp (((2 : ℕ) : ℝ) * -t) * ((1 - 2 * t) * exp (2 * t + (2 * t) ^ 2)) =
        exp (((2 : ℕ) : ℝ) * (((2 : ℝ≥0) : ℝ) ^ 2 * t ^ 2 / 2)) * (1 - 2 * t) := by
      rw [mul_left_comm, ← exp_add]
      push_cast
      ring_nf
    calc exp (((2 : ℕ) : ℝ) * -t) ≤
        exp (((2 : ℕ) : ℝ) * -t) * ((1 - 2 * t) * exp (2 * t + (2 * t) ^ 2)) :=
          le_mul_of_one_le_right (exp_pos _).le key
      _ = _ := hexp

/-- **Tail bound for the `χ²_n` distribution** (Wainwright, *High-Dimensional Statistics*, 2019,
§2.1.3, the `χ²` tail example; Rinaldo 2017, Example 3.8): if `Z₁, …, Zₙ` are independent standard
normal variables, then
`P(|(1/n) ∑ Zₖ² - 1| ≥ t) ≤ 2 exp (-n t² / 8)` for every `t ∈ (0, 1)`. Here the `Zₖ` are the
coordinates on `Fin n → ℝ` under the product measure. -/
public theorem measureReal_abs_chiSq_mean_sub_one_ge_le (n : ℕ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).real
        {z | t ≤ |(1 / (n : ℝ)) * ∑ k, z k ^ 2 - 1|} ≤ 2 * exp (-(n : ℝ) * t ^ 2 / 8) := by
  set P := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: the bound is `2`.
    simp only [Nat.cast_zero, neg_zero, zero_mul, zero_div, exp_zero, mul_one]
    linarith [measureReal_le_one (μ := P) (s := {z | t ≤ |(1 / ((0 : ℕ) : ℝ)) *
      ∑ k, z k ^ 2 - 1|})]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- The centred squares `Y k = Z_k² - 1` are independent and sub-exponential with `(2, 4)`.
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun k z ↦ z k ^ 2 - 1 with hY
  have hind : iIndepFun Y P :=
    iIndepFun_pi (X := fun _ (x : ℝ) ↦ x ^ 2 - 1) fun _ ↦ by fun_prop
  have hmeas : ∀ k, Measurable (Y k) := fun k ↦ by fun_prop
  have hsub : ∀ k, HasSubexponentialMGF (Y k) 2 4 P := fun k ↦ by
    have hk := measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) k
    refine HasSubexponentialMGF.of_map (X := fun x : ℝ ↦ x ^ 2 - 1) hk.measurable.aemeasurable ?_
    rw [hk.map_eq]
    exact hasSubexponentialMGF_sq_sub_one_gaussianReal
  have hS := HasSubexponentialMGF.sum_of_iIndepFun hind hmeas (s := Finset.univ)
    fun k _ ↦ hsub k
  have hν : ((NNReal.sqrt (∑ _k : Fin n, (2 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) ^ 2 = 4 * n := by
    rw [Real.coe_sqrt, Real.sq_sqrt (NNReal.coe_nonneg _)]
    push_cast
    simp [Finset.sum_const, Finset.card_univ]
    ring
  set S := ∑ k, Y k with hS_def
  have hSz : ∀ z, S z = ∑ k, z k ^ 2 - n := fun z ↦ by
    simp [hS_def, hY, Finset.sum_apply, Finset.sum_sub_distrib]
  -- The event in terms of `S`.
  have hsubset : {z | t ≤ |(1 / (n : ℝ)) * ∑ k, z k ^ 2 - 1|} ⊆
      {z | n * t ≤ S z} ∪ {z | n * t ≤ (-S) z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, hSz] at hz ⊢
    have heq : (1 / (n : ℝ)) * ∑ k, z k ^ 2 - 1 = (∑ k, z k ^ 2 - n) / n := by
      field_simp
    rw [heq, abs_div, abs_of_pos hn', le_div_iff₀ hn', mul_comm] at hz
    rcases le_abs'.mp hz with h | h
    · right; linarith
    · left; exact h
  have htα : ((4 : ℝ≥0) : ℝ) * (n * t) ≤
      ((NNReal.sqrt (∑ _k : Fin n, (2 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) ^ 2 := by
    rw [hν]
    push_cast
    nlinarith
  have hup := hS.measureReal_ge_le_of_le (by positivity) htα
  have hlow := hS.neg.measureReal_ge_le_of_le (by positivity) htα
  have hval : -(n * t) ^ 2 / (2 * ((NNReal.sqrt (∑ _k : Fin n, (2 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) ^ 2) =
      -(n : ℝ) * t ^ 2 / 8 := by
    rw [hν]
    field_simp
    ring
  rw [hval] at hup hlow
  calc P.real {z | t ≤ |(1 / (n : ℝ)) * ∑ k, z k ^ 2 - 1|}
      ≤ P.real ({z | n * t ≤ S z} ∪ {z | n * t ≤ (-S) z}) := measureReal_mono hsubset
    _ ≤ P.real {z | n * t ≤ S z} + P.real {z | n * t ≤ (-S) z} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end

end MathlibExt.Probability.HighDimensionalStatisticsWanted
