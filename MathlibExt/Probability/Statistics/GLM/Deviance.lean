/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.CountData.ExactTest
public import MathlibExt.Probability.Statistics.GoodnessOfFit.Pearson
public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Chi-square calibration of the Poisson / multinomial deviance

For cell counts `N` and fitted means `Eᵢ = n pᵢ`, the deviance of the Poisson log-linear model
is the sum of unit Poisson deviances (`CountData.poissonDeviance`),
`D = ∑ᵢ 2 (Nᵢ log (Nᵢ / Eᵢ) - (Nᵢ - Eᵢ))` (`devianceStatistic`). When the counts sum to `n` and
the probabilities to `1` the linear terms cancel and `D = 2 ∑ᵢ Nᵢ log (Nᵢ / (n pᵢ))`
(`devianceStatistic_eq_two_mul_sum`), the likelihood-ratio (`G²`) statistic of the multinomial
model against its saturated fit. This file proves that the deviance has the same chi-square
limit as Pearson's statistic `X² = ∑ᵢ (Nᵢ - Eᵢ)² / Eᵢ`, so the usual chi-square calibration of
the deviance holds for a fixed number of cells, for a simple null and for fitted cell
probabilities.

## Main results

* `abs_poissonDeviance_sub_sq_div_le`: for `N ≥ 0` and `E > 0`, the unit deviance and the
  Pearson term differ by at most `|N - E|³ / E²`. The constant is attained at `N = 0`.
* `abs_devianceStatistic_sub_pearsonStatistic_le`: if every `pᵢ ≥ m > 0` and `n > 0`, then
  `|D - X²| ≤ X² √(X² / (n m))`. The bound depends on the counts only through `X²`.
* `tendstoInMeasure_devianceStatistic_sub_pearsonStatistic`: if `X²ₙ` converges in distribution
  and the (possibly random) cell probabilities stay above a fixed `m > 0` with probability
  tending to `1`, then `Dₙ - X²ₙ → 0` in probability.
* `tendstoInDistribution_devianceStatistic`: **the deviance (`G²`) is asymptotically `χ²_{k-1}`**
  under a simple null with all cell probabilities positive (`k ≥ 2` cells), from Pearson's
  theorem `tendstoInDistribution_pearsonStatistic`.
* `tendstoInDistribution_devianceStatistic_fitted`: with cell probabilities `p(θ̂)` from an
  efficient grouped-count estimator, the deviance is asymptotically `χ²_{k-1-dim V}`, from
  `tendstoInDistribution_pearsonStatistic_fitted`.
  `tendstoInDistribution_devianceStatistic_fitted_of_injective` is the `χ²_{k-1-s}` form.

## Method

With `x = N / E`, the difference between the unit deviance and the Pearson term is
`E (2 x log x + 1 - x²)` (`poissonDeviance_sub_sq_div_eq`), and
`|2 x log x + 1 - x²| ≤ |x - 1|³` for all `x ≥ 0` (`abs_two_mul_mul_log_add_one_sub_sq_le`).
The proof uses that `2 x log x + 1 - x²` is antitone on `(0, ∞)` and vanishes at `1` (its sign),
and the bounds `log x ≥ 2 (x - 1) / (x + 1)` for `x ≥ 1` and `≤` for `0 < x ≤ 1` (its size).
Summing, each cell contributes at most `tᵢ |Nᵢ - Eᵢ| / Eᵢ` with `tᵢ = (Nᵢ - Eᵢ)² / Eᵢ ≤ X²` and
`|Nᵢ - Eᵢ| / Eᵢ ≤ √(X² / (n m))`. Since `X²ₙ` is bounded in probability, `X²ₙ^{3/2} / √n → 0`,
and Slutsky's theorem moves the limit of `X²ₙ` to `Dₙ`. For fitted probabilities, consistency of
`θ̂` (from the efficiency expansion) keeps `p(θ̂)` above half the smallest true probability with
probability tending to `1`.

## Scope

* The number of cells and the null probabilities are fixed as `n → ∞`. Sparse-cell asymptotics
  (`n pᵢ` bounded), where the deviance is not calibrated by `χ²`, are not covered.
* The deviance of a GLM with continuous covariates and one observation per covariate pattern
  has no chi-square limit in general; nothing is claimed about it. The covered case is grouped
  count data with a fixed number of cells, where the deviance compares the model with the
  saturated multinomial model.
* Only the Poisson / multinomial deviance is treated. Scaled deviances of families with a
  dispersion parameter, and differences of deviances between nested models (analysis of
  deviance), are not covered.
* All null cell probabilities must be positive and `k ≥ 2`; the tests show that the deviance is
  identically `0` with a zero-probability cell and does not converge to `χ²₁`.
* The fitted theorem inherits the efficient-estimator hypothesis of
  `tendstoInDistribution_pearsonStatistic_fitted`; it is not derived from the likelihood
  equations.

## References

* S. S. Wilks, *The large-sample distribution of the likelihood ratio for testing composite
  hypotheses*, Ann. Math. Statist. 9 (1938), 60–62.
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman & Hall (1989),
  §5.4.3 and §6.2.
* A. Agresti, *Categorical Data Analysis*, 3rd ed., Wiley (2013), §1.5 and §16.3.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §17.

## Source receipt

Reused: `CountData.poissonDeviance` (`GLM/CountData/ExactTest.lean`); `cellCount`,
`pearsonStatistic`, `tendstoInDistribution_pearsonResidual`,
`tendstoInDistribution_pearsonStatistic`, `tendstoInDistribution_pearsonStatistic_fitted`
(`GoodnessOfFit/Pearson.lean`); `TendstoInDistribution.mul_tendstoInMeasure_zero` and
`tendstoInMeasure_zero_of_abs_le` (`MLEAsymptoticNormality.lean`);
`TendstoInDistribution.smul_of_tendstoInMeasure_const`,
`tendstoInMeasure_of_tendstoInDistribution_const`, `TendstoInMeasure.comp_const_of_continuousAt`
(`Slutsky.lean`). The consistency step of `consistent_of_efficient` repeats the short argument
inside the proof of `tendstoInDistribution_pearsonStatistic_fitted`, which does not export it.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset Real Topology Module
open MathlibExt.Probability.Statistics.GLM.CountData
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.GLM

/-! ### The scalar inequality -/

/-- `log x - 2 (x - 1) / (x + 1)` is monotone on `(0, ∞)`: its derivative is
`(x - 1)² / (x (x + 1)²) ≥ 0`. -/
theorem monotoneOn_log_sub_pade :
    MonotoneOn (fun x : ℝ => log x - 2 * (x - 1) / (x + 1)) (Set.Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (f' := fun x => x⁻¹ - (2 * 1 * (x + 1) - 2 * (x - 1) * 1) / (x + 1) ^ 2) ?_ ?_ ?_
  · intro x hx
    have hx : (0 : ℝ) < x := hx
    have h1 : x + 1 ≠ 0 := by positivity
    exact (((continuousAt_log hx.ne').sub
      ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
        (continuousAt_id.add continuousAt_const) h1))).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : (0 : ℝ) < x := hx
    have h1 : x + 1 ≠ 0 := by positivity
    exact ((hasDerivAt_log hx.ne').sub
      ((((hasDerivAt_id' x).sub_const 1).const_mul 2).div
        ((hasDerivAt_id' x).add_const 1) h1)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : (0 : ℝ) < x := hx
    have h : 0 ≤ (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by positivity
    convert h using 1
    field_simp
    ring

/-- `2 x log x + 1 - x²` is antitone on `(0, ∞)`: its derivative `2 (log x + 1 - x)` is
nonpositive. -/
theorem antitoneOn_two_mul_mul_log_add_one_sub_sq :
    AntitoneOn (fun x : ℝ => 2 * x * log x + 1 - x ^ 2) (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun x => 2 * log x + 2 - 2 * x) ?_ ?_ ?_
  · intro x hx
    have hx : (0 : ℝ) < x := hx
    exact (((continuousAt_const.mul continuousAt_id).mul (continuousAt_log hx.ne')).add
      continuousAt_const |>.sub (continuousAt_id.pow 2)).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : (0 : ℝ) < x := hx
    have h := ((((hasDerivAt_id' x).const_mul 2).mul (hasDerivAt_log hx.ne')).add_const 1).sub
      (hasDerivAt_pow 2 x)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    field_simp
    ring
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : (0 : ℝ) < x := hx
    linarith [log_le_sub_one_of_pos hx]

/-- **The cubic bound.** For every `x ≥ 0`, `|2 x log x + 1 - x²| ≤ |x - 1|³`. (At `x = 0`,
where `log 0 = 0`, both sides are `1`.) -/
theorem abs_two_mul_mul_log_add_one_sub_sq_le {x : ℝ} (hx : 0 ≤ x) :
    |2 * x * log x + 1 - x ^ 2| ≤ |x - 1| ^ 3 := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  have hx1 : 0 < x + 1 := by linarith
  have hmono := monotoneOn_log_sub_pade
  have hanti := antitoneOn_two_mul_mul_log_add_one_sub_sq
  have h1mem : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have hxmem : x ∈ Set.Ioi 0 := hx
  rcases le_total 1 x with h | h
  · -- `x ≥ 1`: the expression is `≤ 0` and `≥ -(x - 1)³ / (x + 1)`.
    have hE : 2 * x * log x + 1 - x ^ 2 ≤ 0 := by
      have := hanti h1mem hxmem h
      simpa using this
    have hL : 2 * (x - 1) ≤ log x * (x + 1) := by
      have := hmono h1mem hxmem h
      simp only [log_one, sub_self, mul_zero, zero_div] at this
      exact (div_le_iff₀ hx1).1 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 * x)
    have h3 : 0 ≤ (x - 1) ^ 3 * x := by
      have : 0 ≤ x - 1 := by linarith
      positivity
    rw [abs_of_nonpos hE, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1)]
    refine le_of_mul_le_mul_right ?_ hx1
    nlinarith [h2, h3]
  · -- `0 < x ≤ 1`: the expression is `≥ 0` and `≤ (1 - x)³ / (1 + x)`.
    have hE : 0 ≤ 2 * x * log x + 1 - x ^ 2 := by
      have := hanti hxmem h1mem h
      simpa using this
    have hL : log x * (x + 1) ≤ 2 * (x - 1) := by
      have := hmono hxmem h1mem h
      simp only [log_one, sub_self, mul_zero, zero_div] at this
      exact (le_div_iff₀ hx1).1 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 * x)
    have h3 : 0 ≤ (1 - x) ^ 3 * x := by
      have : 0 ≤ 1 - x := by linarith
      positivity
    rw [abs_of_nonneg hE, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    refine le_of_mul_le_mul_right ?_ hx1
    nlinarith [h2, h3]

/-! ### Unit deviance against the Pearson term -/

/-- With `x = N / E`, the unit deviance minus the Pearson term is `E (2 x log x + 1 - x²)`. -/
theorem poissonDeviance_sub_sq_div_eq {N E : ℝ} (hE : 0 < E) :
    poissonDeviance N E - (N - E) ^ 2 / E =
      E * (2 * (N / E) * log (N / E) + 1 - (N / E) ^ 2) := by
  obtain ⟨x, rfl⟩ : ∃ x, N = x * E := ⟨N / E, by field_simp⟩
  have hx : x * E / E = x := mul_div_cancel_right₀ x hE.ne'
  have hsq : (x * E - E) ^ 2 / E = E * (x - 1) ^ 2 := by
    field_simp
  rw [hx, hsq, poissonDeviance, hx]
  ring

/-- **Unit deviance versus Pearson term.** For a count `N ≥ 0` and a mean `E > 0`, the unit
Poisson deviance and the Pearson term `(N - E)² / E` differ by at most `|N - E|³ / E²`. -/
theorem abs_poissonDeviance_sub_sq_div_le {N E : ℝ} (hN : 0 ≤ N) (hE : 0 < E) :
    |poissonDeviance N E - (N - E) ^ 2 / E| ≤ |N - E| ^ 3 / E ^ 2 := by
  rw [poissonDeviance_sub_sq_div_eq hE, abs_mul, abs_of_pos hE]
  have hb := abs_two_mul_mul_log_add_one_sub_sq_le (div_nonneg hN hE.le)
  have hx : |N / E - 1| = |N - E| / E := by
    rw [show N / E - 1 = (N - E) / E by field_simp, abs_div, abs_of_pos hE]
  rw [hx] at hb
  calc E * |2 * (N / E) * log (N / E) + 1 - (N / E) ^ 2|
      ≤ E * (|N - E| / E) ^ 3 := mul_le_mul_of_nonneg_left hb hE.le
    _ = |N - E| ^ 3 / E ^ 2 := by
      field_simp

/-! ### The deviance statistic -/

variable {ι : Type*} [Fintype ι]

/-- The **deviance** of cell counts `N` against cell probabilities `p` with `n` observations:
the sum over cells of the unit Poisson deviances `2 (Nᵢ log (Nᵢ / (n pᵢ)) - (Nᵢ - n pᵢ))`. It is
the Poisson log-linear deviance with fitted means `n pᵢ`, and the multinomial likelihood-ratio
(`G²`) statistic when `∑ Nᵢ = n` and `∑ pᵢ = 1` (`devianceStatistic_eq_two_mul_sum`). -/
noncomputable def devianceStatistic (n : ℕ) (p N : ι → ℝ) : ℝ :=
  ∑ i, poissonDeviance (N i) (n * p i)

/-- **The `G²` form.** When the counts sum to `n` and the probabilities to `1`, the linear terms
of the deviance cancel: `D = 2 ∑ᵢ Nᵢ log (Nᵢ / (n pᵢ))`. -/
theorem devianceStatistic_eq_two_mul_sum {n : ℕ} {p N : ι → ℝ} (hN : ∑ i, N i = n)
    (hp : ∑ i, p i = 1) :
    devianceStatistic n p N = 2 * ∑ i, N i * log (N i / (n * p i)) := by
  have hlin : ∑ i, (N i - n * p i) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, hp, hN, mul_one, sub_self]
  simp only [devianceStatistic, poissonDeviance]
  rw [← mul_sum, sum_sub_distrib, hlin, sub_zero]

/-- **Deviance versus Pearson's statistic.** If `n > 0`, every `pᵢ ≥ m > 0` and every count is
nonnegative, then `|D - X²| ≤ X² √(X² / (n m))`. -/
theorem abs_devianceStatistic_sub_pearsonStatistic_le {n : ℕ} (hn : 0 < n) {p N : ι → ℝ}
    {m : ℝ} (hm : 0 < m) (hpm : ∀ i, m ≤ p i) (hN : ∀ i, 0 ≤ N i) :
    |devianceStatistic n p N - pearsonStatistic n p N| ≤
      pearsonStatistic n p N * √(pearsonStatistic n p N / (n * m)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnm : 0 < (n : ℝ) * m := mul_pos hn' hm
  have hE : ∀ i, 0 < (n : ℝ) * p i := fun i => mul_pos hn' (hm.trans_le (hpm i))
  have hEge : ∀ i, (n : ℝ) * m ≤ n * p i := fun i => mul_le_mul_of_nonneg_left (hpm i) hn'.le
  set X2 := pearsonStatistic n p N with hX2
  have ht0 : ∀ i, 0 ≤ (N i - n * p i) ^ 2 / (n * p i) := fun i => by
    have := hE i
    positivity
  have htle : ∀ i, (N i - n * p i) ^ 2 / (n * p i) ≤ X2 := fun i =>
    single_le_sum (fun j _ => ht0 j) (mem_univ i)
  have hX0 : 0 ≤ X2 := sum_nonneg fun i _ => ht0 i
  have hcell : ∀ i, |poissonDeviance (N i) (n * p i) - (N i - n * p i) ^ 2 / (n * p i)| ≤
      (N i - n * p i) ^ 2 / (n * p i) * √(X2 / (n * m)) := by
    intro i
    refine (abs_poissonDeviance_sub_sq_div_le (hN i) (hE i)).trans ?_
    have hrel : |N i - n * p i| / (n * p i) ≤ √(X2 / (n * m)) := by
      have h := Real.abs_le_sqrt (x := (N i - n * p i) / (n * p i)) (y := X2 / (n * m)) ?_
      · rwa [abs_div, abs_of_pos (hE i)] at h
      · calc ((N i - n * p i) / (n * p i)) ^ 2
            = (N i - n * p i) ^ 2 / (n * p i) / (n * p i) := by
              have := (hE i).ne'
              field_simp
          _ ≤ X2 / (n * m) := div_le_div₀ hX0 (htle i) hnm (hEge i)
    calc |N i - n * p i| ^ 3 / (n * p i) ^ 2
        = (N i - n * p i) ^ 2 / (n * p i) * (|N i - n * p i| / (n * p i)) := by
          rw [← sq_abs (N i - n * p i)]
          have := (hE i).ne'
          field_simp
      _ ≤ (N i - n * p i) ^ 2 / (n * p i) * √(X2 / (n * m)) :=
          mul_le_mul_of_nonneg_left hrel (ht0 i)
  calc |devianceStatistic n p N - X2|
      = |∑ i, (poissonDeviance (N i) (n * p i) - (N i - n * p i) ^ 2 / (n * p i))| := by
        rw [hX2, devianceStatistic, pearsonStatistic, sum_sub_distrib]
    _ ≤ ∑ i, |poissonDeviance (N i) (n * p i) - (N i - n * p i) ^ 2 / (n * p i)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (N i - n * p i) ^ 2 / (n * p i) * √(X2 / (n * m)) :=
        sum_le_sum fun i _ => hcell i
    _ = X2 * √(X2 / (n * m)) := by
        rw [← sum_mul]
        rfl

/-- The deviance is a measurable function of the cell probabilities and counts. -/
theorem measurable_devianceStatistic (n : ℕ) :
    Measurable fun q : (ι → ℝ) × (ι → ℝ) => devianceStatistic n q.1 q.2 := by
  unfold devianceStatistic poissonDeviance
  refine Finset.measurable_sum _ fun i _ => ?_
  fun_prop

/-! ### Transfer of the chi-square limit -/

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The deviance of almost everywhere measurable cell probabilities and counts is almost
everywhere measurable. -/
theorem aemeasurable_devianceStatistic {q N : Ω → ι → ℝ} (hq : AEMeasurable q P)
    (hN : AEMeasurable N P) (n : ℕ) :
    AEMeasurable (fun ω => devianceStatistic n (q ω) (N ω)) P :=
  (measurable_devianceStatistic n).comp_aemeasurable (hq.prodMk hN)

/-- **The deviance and Pearson's statistic are asymptotically equivalent.** Let `pₙ` be (possibly
random) cell probabilities and `Nₙ` nonnegative cell counts. If Pearson's statistic
`X²ₙ = pearsonStatistic n pₙ Nₙ` converges in distribution, and for some `m > 0` the event
`{∀ i, m ≤ pₙ i}` has probability tending to `1`, then `Dₙ - X²ₙ → 0` in probability. -/
theorem tendstoInMeasure_devianceStatistic_sub_pearsonStatistic {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {p N : ℕ → Ω → ι → ℝ} {Z : Ω' → ℝ} {m : ℝ} (hm : 0 < m) (hN : ∀ n ω i, 0 ≤ N n ω i)
    (hT : TendstoInDistribution (fun n ω => pearsonStatistic n (p n ω) (N n ω)) atTop Z
      (fun _ => P) P')
    (hG : Tendsto (fun n => P {ω | ∀ i, m ≤ p n ω i}ᶜ) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => devianceStatistic n (p n ω) (N n ω) -
      pearsonStatistic n (p n ω) (N n ω)) atTop 0 := by
  set T : ℕ → Ω → ℝ := fun n ω => pearsonStatistic n (p n ω) (N n ω) with hT_def
  -- `T^{3/2}` converges in distribution and `(n m)^{-1/2} → 0`.
  have hA : TendstoInDistribution (fun n ω => T n ω * √(T n ω)) atTop
      (fun ω => Z ω * √(Z ω)) (fun _ => P) P' :=
    hT.continuous_comp (g := fun t : ℝ => t * √t) (by fun_prop)
  have hc : Tendsto (fun n : ℕ => √(((n : ℝ) * m)⁻¹)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) * m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hm)
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  have hη : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => √(((n : ℝ) * m)⁻¹)) atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => hc)
  have hV := hA.mul_tendstoInMeasure_zero hη fun _ => aemeasurable_const
  refine tendstoInMeasure_zero_of_abs_le (G := fun n => {ω | 0 < n ∧ ∀ i, m ≤ p n ω i}) hV
    ?_ ?_
  · refine hG.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [hn, true_and]
  · rintro n ω ⟨hn, hω⟩
    have hb := abs_devianceStatistic_sub_pearsonStatistic_le hn hm hω (hN n ω)
    have hT0 : 0 ≤ T n ω := sum_nonneg fun i _ => by
      have : (0 : ℝ) < n * p n ω i := mul_pos (Nat.cast_pos.2 hn) (hm.trans_le (hω i))
      positivity
    refine hb.trans (le_of_eq ?_)
    change T n ω * √(T n ω / (n * m)) = T n ω * √(T n ω) * √(((n : ℝ) * m)⁻¹)
    rw [div_eq_mul_inv, Real.sqrt_mul hT0, mul_assoc]

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- The cell counts of measurable observations are almost everywhere measurable. -/
theorem aemeasurable_cellCount [Finite ι] [DecidableEq ι] {X : ℕ → Ω → ι}
    (hX : ∀ k, AEMeasurable (X k) P) (n : ℕ) : AEMeasurable (fun ω => cellCount X n ω) P := by
  refine AEMeasurable.of_eval fun i => ?_
  simp only [cellCount]
  exact Finset.aemeasurable_fun_sum _ fun k _ =>
    (Measurable.of_discrete (f := fun j : ι => if j = i then (1 : ℝ) else 0)).comp_aemeasurable
      (hX k)

/-- **Chi-square calibration of the deviance (simple null).** For i.i.d. categorical
observations with cell probabilities `pᵢ > 0` on `k ≥ 2` cells, the deviance
`Dₙ = ∑ᵢ 2 (Nᵢ log (Nᵢ / (n pᵢ)) - (Nᵢ - n pᵢ)) = 2 ∑ᵢ Nᵢ log (Nᵢ / (n pᵢ))` of the cell counts
converges in distribution to `χ²_{k-1}`. -/
theorem tendstoInDistribution_devianceStatistic [DecidableEq ι] {X : ℕ → Ω → ι} {p : ι → ℝ}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = p i) (hpos : ∀ i, 0 < p i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hk : 2 ≤ Fintype.card ι) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquareMeasure (Fintype.card ι - 1)) P') :
    TendstoInDistribution (fun n ω => devianceStatistic n p (cellCount X n ω)) atTop Z
      (fun _ => P) P' := by
  have hT := tendstoInDistribution_pearsonStatistic hX0 hpos hindep hident hk hZ
  obtain ⟨m, hm, hpm⟩ : ∃ m, 0 < m ∧ ∀ i, m ≤ p i := by
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min p
    exact ⟨p i₀, hpos i₀, hi₀⟩
  have hN : ∀ n ω i, 0 ≤ cellCount X n ω i := fun n ω i =>
    sum_nonneg fun k _ => by split_ifs <;> norm_num
  have hempty : {ω : Ω | ∀ i, m ≤ p i}ᶜ = ∅ := by
    simp [hpm]
  have hG : Tendsto (fun _ : ℕ => P {ω : Ω | ∀ i, m ≤ p i}ᶜ) atTop (𝓝 0) := by
    rw [hempty, measure_empty]
    exact tendsto_const_nhds
  have hsub : TendstoInMeasure P (fun n ω => devianceStatistic n p (cellCount X n ω) -
      pearsonStatistic n p (cellCount X n ω)) atTop 0 :=
    tendstoInMeasure_devianceStatistic_sub_pearsonStatistic (p := fun _ _ => p)
      (N := fun n ω => cellCount X n ω) hm hN hT hG
  have hmeas : ∀ n, AEMeasurable (fun ω => devianceStatistic n p (cellCount X n ω)) P := fun n =>
    aemeasurable_devianceStatistic (q := fun _ => p) (N := fun ω => cellCount X n ω)
      aemeasurable_const (aemeasurable_cellCount (fun k => (hident k).aemeasurable_fst) n) n
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ω => devianceStatistic n p (cellCount X n ω)) Z hT hsub hmeas

omit [Fintype ι] in
/-- **Consistency of an efficient estimator.** Under the efficiency expansion
`√n (θ̂ - θ₀) = L(Rₙ) + o_P(1)` of `tendstoInDistribution_pearsonStatistic_fitted`, with `Rₙ` the
Pearson residuals at `θ₀`, the estimator is consistent: `θ̂ → θ₀` in probability. -/
theorem consistent_of_efficient [Finite ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {X : ℕ → Ω → ι} {p : ι → ℝ} {θ₀ : F}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = p i) (hpos : ∀ i, 0 < p i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    {L : EuclideanSpace ℝ ι →L[ℝ] F} {θhat : ℕ → Ω → F} (hθm : ∀ n, AEMeasurable (θhat n) P)
    (hθ : TendstoInMeasure P (fun (n : ℕ) ω => √n • (θhat n ω - θ₀) -
      L (pearsonResidual n p (cellCount X n ω))) atTop 0) :
    TendstoInMeasure P θhat atTop (fun _ => θ₀) := by
  have : Fintype ι := Fintype.ofFinite ι
  set R : ℕ → Ω → EuclideanSpace ℝ ι := fun n ω => pearsonResidual n p (cellCount X n ω)
    with hR_def
  have hR := tendstoInDistribution_pearsonResidual hX0 hpos hindep hident
  set S : ℕ → Ω → F := fun n ω => √n • (θhat n ω - θ₀) with hS_def
  have hSm : ∀ n, AEMeasurable (S n) P := fun n => ((hθm n).sub_const θ₀).const_smul _
  have hRL := hR.continuous_comp (g := fun v => L v) L.continuous
  have hScl : TendstoInDistribution S atTop _ (fun _ => P) _ :=
    tendstoInDistribution_of_tendstoInMeasure_sub S _ hRL hθ hSm
  have hsqrt : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => (√(n : ℝ))⁻¹) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_inv_atTop_zero.comp hsqrt)
  have h1 : TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • S n ω) atTop
      (fun _ => (0 : F)) (fun _ => P) (stdGaussian (EuclideanSpace ℝ ι)) :=
    (hScl.smul_of_tendstoInMeasure_const hinv fun _ => aemeasurable_const).congr
      (fun _ => ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => zero_smul ℝ _)
  have h := (tendstoInMeasure_of_tendstoInDistribution_const h1).congr'
    (f' := fun n ω => θhat n ω - θ₀) ?_ EventuallyEq.rfl
  · rw [tendstoInMeasure_iff_norm] at h ⊢
    simpa using h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
    exact ae_of_all _ fun ω => by simp [S, smul_smul, inv_mul_cancel₀ hs]

/-- **Chi-square calibration of the deviance with fitted cell probabilities.** Under the
hypotheses of `tendstoInDistribution_pearsonStatistic_fitted` (a differentiable model `pθ` with
weighted tangent space `V = range J`, and an efficient grouped-count estimator `θ̂`), the
deviance with fitted probabilities, `∑ᵢ 2 (Nᵢ log (Nᵢ / (n pᵢ(θ̂))) - (Nᵢ - n pᵢ(θ̂)))`, converges
in distribution to `χ²_{k-1-dim V}`. -/
theorem tendstoInDistribution_devianceStatistic_fitted [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {X : ℕ → Ω → ι} {pθ : F → ι → ℝ} {θ₀ : F}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = pθ θ₀ i) (hpos : ∀ i, 0 < pθ θ₀ i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hnn : ∀ θ i, 0 ≤ pθ θ i) (hsum : ∀ᶠ θ in 𝓝 θ₀, ∑ i, pθ θ i = 1) (hmeas : Measurable pθ)
    {D : F →L[ℝ] (ι → ℝ)} (hD : HasFDerivAt pθ D θ₀)
    {J : F →L[ℝ] EuclideanSpace ℝ ι} (hJ : ∀ a i, J a i = D a i / √(pθ θ₀ i))
    {L : EuclideanSpace ℝ ι →L[ℝ] F}
    (hJL : ∀ v, J (L v) = (LinearMap.range J.toLinearMap).starProjection v)
    {θhat : ℕ → Ω → F} (hθm : ∀ n, AEMeasurable (θhat n) P)
    (hθ : TendstoInMeasure P (fun (n : ℕ) ω => √n • (θhat n ω - θ₀) -
      L (pearsonResidual n (pθ θ₀) (cellCount X n ω))) atTop 0)
    (hdf : finrank ℝ (LinearMap.range J.toLinearMap) + 1 < Fintype.card ι)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z (chiSquareMeasure
      (Fintype.card ι - 1 - finrank ℝ (LinearMap.range J.toLinearMap))) P') :
    TendstoInDistribution (fun n ω => devianceStatistic n (pθ (θhat n ω)) (cellCount X n ω))
      atTop Z (fun _ => P) P' := by
  have hT := tendstoInDistribution_pearsonStatistic_fitted hX0 hpos hindep hident hnn hsum hmeas
    hD hJ hJL hθm hθ hdf hZ
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min (pθ θ₀)
  set m := pθ θ₀ i₀ / 2 with hm_def
  have hm : 0 < m := half_pos (hpos i₀)
  -- The fitted probabilities stay above `m` with probability tending to `1`.
  have hcons := consistent_of_efficient hX0 hpos hindep hident hθm hθ
  have hpc : TendstoInMeasure P (fun n ω => pθ (θhat n ω)) atTop (fun _ => pθ θ₀) :=
    hcons.comp_const_of_continuousAt hD.continuousAt
  rw [tendstoInMeasure_iff_dist] at hpc
  have hG : Tendsto (fun n => P {ω | ∀ i, m ≤ pθ (θhat n ω) i}ᶜ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hpc m hm)
      (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω ⊢
    obtain ⟨i, hi⟩ := hω
    have h2m : 2 * m ≤ pθ θ₀ i := by rw [hm_def]; linarith [hi₀ i]
    have hdi : m ≤ dist (pθ (θhat n ω) i) (pθ θ₀ i) := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    exact hdi.trans (dist_le_pi_dist _ _ i)
  have hN : ∀ n ω i, 0 ≤ cellCount X n ω i := fun n ω i =>
    sum_nonneg fun k _ => by split_ifs <;> norm_num
  have hsub : TendstoInMeasure P (fun n ω => devianceStatistic n (pθ (θhat n ω))
      (cellCount X n ω) - pearsonStatistic n (pθ (θhat n ω)) (cellCount X n ω)) atTop 0 :=
    tendstoInMeasure_devianceStatistic_sub_pearsonStatistic
      (p := fun n ω => pθ (θhat n ω)) (N := fun n ω => cellCount X n ω) hm hN hT hG
  have hDm : ∀ n, AEMeasurable
      (fun ω => devianceStatistic n (pθ (θhat n ω)) (cellCount X n ω)) P :=
    fun n => aemeasurable_devianceStatistic (q := fun ω => pθ (θhat n ω))
      (N := fun ω => cellCount X n ω) (hmeas.comp_aemeasurable (hθm n))
      (aemeasurable_cellCount (fun k => (hident k).aemeasurable_fst) n) n
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ω => devianceStatistic n (pθ (θhat n ω)) (cellCount X n ω)) Z hT hsub hDm

/-- **Chi-square calibration of the deviance with `s` fitted parameters**: the form of
`tendstoInDistribution_devianceStatistic_fitted` for an injective weighted Jacobian, with limit
`χ²_{k-1-s}`, `s = dim F`. -/
theorem tendstoInDistribution_devianceStatistic_fitted_of_injective [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] {X : ℕ → Ω → ι} {pθ : F → ι → ℝ} {θ₀ : F}
    (hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = pθ θ₀ i) (hpos : ∀ i, 0 < pθ θ₀ i)
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hnn : ∀ θ i, 0 ≤ pθ θ i) (hsum : ∀ᶠ θ in 𝓝 θ₀, ∑ i, pθ θ i = 1) (hmeas : Measurable pθ)
    {D : F →L[ℝ] (ι → ℝ)} (hD : HasFDerivAt pθ D θ₀)
    {J : F →L[ℝ] EuclideanSpace ℝ ι} (hJ : ∀ a i, J a i = D a i / √(pθ θ₀ i))
    (hinj : Function.Injective J) {L : EuclideanSpace ℝ ι →L[ℝ] F}
    (hJL : ∀ v, J (L v) = (LinearMap.range J.toLinearMap).starProjection v)
    {θhat : ℕ → Ω → F} (hθm : ∀ n, AEMeasurable (θhat n) P)
    (hθ : TendstoInMeasure P (fun (n : ℕ) ω => √n • (θhat n ω - θ₀) -
      L (pearsonResidual n (pθ θ₀) (cellCount X n ω))) atTop 0)
    (hdf : finrank ℝ F + 1 < Fintype.card ι)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure (Fintype.card ι - 1 - finrank ℝ F)) P') :
    TendstoInDistribution (fun n ω => devianceStatistic n (pθ (θhat n ω)) (cellCount X n ω))
      atTop Z (fun _ => P) P' := by
  have hr : finrank ℝ (LinearMap.range J.toLinearMap) = finrank ℝ F :=
    LinearMap.finrank_range_of_inj hinj
  exact tendstoInDistribution_devianceStatistic_fitted hX0 hpos hindep hident hnn hsum hmeas hD
    hJ hJL hθm hθ (by rwa [hr]) (by rwa [hr])

end Probability

end MathlibExt.Probability.Statistics.GLM
