/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.Deviance
public import MathlibExtTest.Probability.Statistics.GoodnessOfFit.Pearson

/-!
# Tests for the chi-square calibration of the deviance

* Concrete values of `devianceStatistic`, computed from the definition, and the same value from
  the `G²` form.
* The constant `1` of the unit bound is attained at `N = 0`, computed from the definition.
* `n > 0` is needed in the statistic bound: with `n = 0` and a single unit count the deviance
  is `-2` while Pearson's statistic is `0`, so the bound fails although `m > 0`, `pᵢ ≥ m` and
  `Nᵢ ≥ 0` hold.
* Non-vacuity: fair coin flips satisfy every hypothesis of the simple-null theorem (limit `χ²₁`);
  the one-parameter model of the Pearson tests with the oracle efficient estimator satisfies the
  fitted theorem (limit `χ²_{3-1-1} = χ²₁`).
* Boundary: with a zero-probability cell every other hypothesis of the simple-null theorem holds,
  the deviance is identically `0`, computed from the definition, and it does not converge to
  `χ²₁`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Module Real
open MathlibExt.Probability.Statistics.GLM MathlibExt.Probability.Statistics.GLM.CountData
open PearsonTest
open scoped NNReal RealInnerProductSpace

namespace MathlibExtTest.Probability.Statistics.GLM.Deviance

/-! ### Concrete values -/

/-- Counts `(2, 0)` against `p = (1/2, 1/2)` with `n = 2`: the cells contribute
`2 (2 log 2 - 1)` and `2`, so the deviance is `4 log 2`. -/
example : devianceStatistic 2 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 2 else 0) =
    4 * log 2 := by
  simp [devianceStatistic, poissonDeviance]
  ring

/-- The same value from the `G²` form `2 ∑ Nᵢ log (Nᵢ / (n pᵢ))`. -/
example : devianceStatistic 2 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 2 else 0) =
    4 * log 2 := by
  rw [devianceStatistic_eq_two_mul_sum (by norm_num) (by norm_num)]
  simp
  ring

/-- The cubic bound on the unit deviance is attained at `N = 0`: the unit deviance is `2 E`, the
Pearson term is `E`, and `|0 - E|³ / E² = E`. -/
example {E : ℝ} (hE : 0 < E) :
    poissonDeviance 0 E - (0 - E) ^ 2 / E = |0 - E| ^ 3 / E ^ 2 := by
  rw [poissonDeviance_zero_left, zero_sub, abs_neg, abs_of_pos hE]
  field_simp
  ring

/-- Counts `(3, 1)` against `p = (1/2, 1/2)` with `n = 4`, from the definition: the cells
contribute `2 (3 log (3/2) - 1)` and `2 (log (1/2) + 1)`, so `D = 6 log 3 - 8 log 2`. -/
example : devianceStatistic 4 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 3 else 1) =
    6 * log 3 - 8 * log 2 := by
  have h32 : log (3 / 2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have h12 : log (1 / 2 : ℝ) = - log 2 := by rw [one_div, log_inv]
  simp only [devianceStatistic, poissonDeviance, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  norm_num [h32, h12]
  ring

/-- The bound applied to counts `(3, 1)` against `p = (1/2, 1/2)` with `n = 4` (`X² = 1`,
`m = 1/2`). -/
example : |devianceStatistic 4 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 3 else 1) - 1| ≤
    √(1 / 2) := by
  have hX : pearsonStatistic 4 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 3 else 1) = 1 := by
    simp [pearsonStatistic]
    norm_num
  have h := abs_devianceStatistic_sub_pearsonStatistic_le (n := 4) (by norm_num)
    (p := fun _ : Bool => (1 / 2 : ℝ)) (N := fun b => if b then 3 else 1) (m := 1 / 2)
    (by norm_num) (fun _ => le_rfl) (fun b => by cases b <;> norm_num)
  rw [hX] at h
  convert h using 2
  norm_num

/-- With `n = 0` every fitted mean is `0`, a unit count contributes
`2 (1 · log (1 / 0) - 1) = -2` (Lean's `x / 0 = 0` and `log 0 = 0`), and Pearson's statistic is
`0`. -/
theorem devianceStatistic_zero_obs :
    devianceStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = -2 ∧
    pearsonStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = 0 := by
  constructor <;> simp [devianceStatistic, poissonDeviance, pearsonStatistic]

/-- **`n > 0` is needed.** With `n = 0`, `p = 1`, `m = 1` and `N = 1` the other hypotheses of
`abs_devianceStatistic_sub_pearsonStatistic_le` hold (`0 < m`, `m ≤ pᵢ`, `0 ≤ Nᵢ`), but its
conclusion fails: `|D - X²| = 2` while the right side is `0`. -/
example : (0 : ℝ) < 1 ∧ (∀ _ : Unit, (1 : ℝ) ≤ 1) ∧ (∀ _ : Unit, (0 : ℝ) ≤ 1) ∧
    ¬ |devianceStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) -
        pearsonStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1)| ≤
      pearsonStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) *
        √(pearsonStatistic 0 (fun _ : Unit => (1 : ℝ)) (fun _ => 1) / ((0 : ℕ) * 1)) := by
  obtain ⟨hD, hX⟩ := devianceStatistic_zero_obs
  refine ⟨one_pos, fun _ => le_rfl, fun _ => zero_le_one, ?_⟩
  rw [hD, hX]
  norm_num

/-! ### Non-vacuity: the simple null -/

/-- **The deviance of fair coin flips converges to `χ²₁`**: every hypothesis of
`tendstoInDistribution_devianceStatistic` holds. -/
example :
    TendstoInDistribution
      (fun n ω => devianceStatistic n (fun _ : Bool => (1 / 2 : ℝ))
        (cellCount (fun k (ω : ℕ → Bool) => ω k) n ω))
      atTop id (fun _ => flips) (chiSquareMeasure 1) :=
  tendstoInDistribution_devianceStatistic flips_real_eval_zero (fun _ => by norm_num)
    iIndepFun_flips identDistrib_flips (by simp) hasLaw_id_chiSquare_card_bool

/-! ### Non-vacuity: one fitted parameter -/

/-- **The fitted deviance with one parameter converges to `χ²₁`.** For the model `model3`
(`k = 3`, `s = 1`) of the Pearson tests and the oracle efficient estimator
`θ̂ n = n^{-1/2} L(Rₙ)`, every hypothesis of
`tendstoInDistribution_devianceStatistic_fitted_of_injective` holds, with limit
`χ²_{3-1-1} = χ²₁`. This runs the consistency step with a nonzero tangent space. -/
example :
    TendstoInDistribution
      (fun n ω => devianceStatistic n (model3 (oracle n ω))
        (cellCount (fun k (ω : ℕ → Fin 3) => ω k) n ω))
      atTop id (fun _ => rolls) (chiSquareMeasure 1) := by
  have hpos : ∀ i, 0 < model3 0 i := fun i => by rw [model3_zero]; norm_num
  have hres := tendstoInDistribution_pearsonResidual rolls_real_eval_zero hpos iIndepFun_rolls
    identDistrib_rolls
  have hθm : ∀ n, AEMeasurable (oracle n) rolls := fun n =>
    (L3.continuous.measurable.comp_aemeasurable (hres.forall_aemeasurable n)).const_mul _
  have hzero : (fun (n : ℕ) (ω : ℕ → Fin 3) => √(n : ℝ) • (oracle n ω - 0) - L3 (res3 n ω)) =
      fun _ _ => 0 := by
    ext n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : res3 0 ω = 0 := by
        ext i
        simp [res3, pearsonResidual]
      simp [h0]
    · have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
      simp [oracle, ← mul_assoc, mul_inv_cancel₀ hs]
  have hθ : TendstoInMeasure rolls
      (fun (n : ℕ) ω => √(n : ℝ) • (oracle n ω - 0) - L3 (res3 n ω)) atTop 0 := by
    rw [hzero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_const_nhds)
  have hdf : Fintype.card (Fin 3) - 1 - finrank ℝ ℝ = 1 := by simp
  have hZ : HasLaw (id : ℝ → ℝ) (chiSquareMeasure (Fintype.card (Fin 3) - 1 - finrank ℝ ℝ))
      (chiSquareMeasure 1) := by
    rw [hdf]
    exact HasLaw.id
  exact tendstoInDistribution_devianceStatistic_fitted_of_injective (θ₀ := 0)
    (D := (1 : ℝ →L[ℝ] ℝ).smulRight dir3) (J := J3) (L := L3)
    rolls_real_eval_zero hpos iIndepFun_rolls identDistrib_rolls model3_nonneg
    (Eventually.of_forall model3_sum) (by fun_prop) hasFDerivAt_model3
    (fun a i => by simp [model3_zero]; ring)
    (fun a b h => smul_left_injective ℝ jvec_ne_zero (by simpa using h)) J3_L3 hθm hθ
    (by simp) hZ

/-! ### Boundary: a zero-probability cell -/

/-- With `p = (1, 0)` every observation lands in the first cell, which contributes
`2 (n log (n / n) - 0) = 0`; the empty second cell has mean `0` and contributes
`2 (0 · log 0 - 0) = 0`. So the deviance is identically `0`. -/
theorem devianceStatistic_degenerate (n : ℕ) (ω : ℕ → Unit) :
    devianceStatistic n (fun b : Bool => if b then 1 else 0)
      (cellCount (fun _ (_ : ℕ → Unit) => true) n ω) = 0 := by
  simp [devianceStatistic, poissonDeviance, cellCount]

/-- **The positivity hypothesis cannot be dropped.** For `p = (1, 0)` and constant observations
every hypothesis of `tendstoInDistribution_devianceStatistic` except positivity holds
(`degenerate_hypotheses`: the cell law, independence, identical distribution and `k = 2 ≥ 2`;
`hZ` holds for `id` under `χ²₁`), and the deviance does not converge to `χ²_{k-1} = χ²₁`: it is
identically `0`, and `χ²₁` has no atom at `0`. -/
example :
    ((∀ b, point.real ((fun _ : ℕ → Unit => true) ⁻¹' {b}) = if b then 1 else 0) ∧
      iIndepFun (fun (_ : ℕ) (_ : ℕ → Unit) => true) point ∧
      (∀ _ : ℕ, IdentDistrib (fun _ : ℕ → Unit => true) (fun _ : ℕ → Unit => true) point point) ∧
      2 ≤ Fintype.card Bool ∧ ¬ ∀ b : Bool, 0 < (if b then (1 : ℝ) else 0)) ∧
    HasLaw (id : ℝ → ℝ) (chiSquareMeasure (Fintype.card Bool - 1)) (chiSquareMeasure 1) ∧
    ¬ TendstoInDistribution
      (fun n ω => devianceStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω))
      atTop id (fun _ => point) (chiSquareMeasure 1) := by
  refine ⟨degenerate_hypotheses, hasLaw_id_chiSquare_card_bool, fun h => ?_⟩
  have h0 : TendstoInDistribution
      (fun n ω => devianceStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω))
      atTop (fun _ : ℕ → Unit => (0 : ℝ)) (fun _ => point) point := by
    have hfun : (fun n (ω : ℕ → Unit) => devianceStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω)) = fun _ _ => (0 : ℝ) := by
      ext n ω
      exact devianceStatistic_degenerate n ω
    rw [hfun]
    exact tendstoInDistribution_const aemeasurable_const
  have heq := tendstoInDistribution_unique _ h h0
  have h1 : chiSquareMeasure 1 {0} = 0 := chiSquareMeasure_singleton 1 0
  rw [Measure.map_id] at heq
  rw [heq] at h1
  simp at h1

end MathlibExtTest.Probability.Statistics.GLM.Deviance
