/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GoodnessOfFit.Pearson
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Pearson's chi-square goodness-of-fit asymptotics

* Concrete values of `cellCount`, `pearsonStatistic` and `pearsonResidual`.
* One cell: the statistic is identically `0` (why `k ≥ 2` is assumed).
* The limit of the residuals is singular: zero variance in the direction `√p`.
* Non-vacuity: fair coin flips on `ℕ → Bool` satisfy every hypothesis of Pearson's theorem,
  giving the `χ²₁` limit; the fitted theorem with a zero-dimensional parameter space recovers it.
* Boundary: with a zero-probability cell (`p = (1, 0)`) the statistic is identically `0` and does
  not converge to `χ²₁`, so the positivity hypothesis cannot be dropped.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Module
open scoped Real NNReal RealInnerProductSpace

namespace PearsonTest

/-! ### Concrete values -/

/-- Four alternating observations put two in each cell. -/
example : cellCount (fun k (_ : Unit) => decide (k % 2 = 0)) 4 () true = 2 := by
  simp only [cellCount, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Counts `(3, 1)` against `p = (1/2, 1/2)` with `n = 4`: `1²/2 + 1²/2 = 1`. -/
example : pearsonStatistic 4 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 3 else 1) = 1 := by
  simp [pearsonStatistic]
  norm_num

/-- The same value as the squared norm of the residual vector. -/
example :
    ‖pearsonResidual 4 (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then 3 else 1)‖ ^ 2 = 1 := by
  rw [norm_sq_pearsonResidual (fun _ => by norm_num)]
  simp [pearsonStatistic]
  norm_num

/-! ### One cell -/

/-- With one cell every observation lands in it and the statistic vanishes, while
`chiSquareMeasure 0` is the zero measure; hence `k ≥ 2` in Pearson's theorem. -/
example (n : ℕ) : pearsonStatistic n (fun _ : Unit => 1) (fun _ => n) = 0 := by
  simp [pearsonStatistic]

/-! ### The singular Gaussian limit -/

/-- The residual limit has variance `0` in the direction `√p`: its covariance `I - √p √pᵀ` is
singular. -/
example {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    HasLaw (fun z => ⟪(ℝ ∙ (WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι))ᗮ.starProjection z,
      (WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι)⟫) (gaussianReal 0 0)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have h := hasLaw_inner_starProjection_orthogonal_sqrt hp₀ hp₁
    (WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι)
  have hn : ‖(WithLp.toLp 2 fun i => √(p i) : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, ← hp₁]
    simp [Real.sq_sqrt (hp₀ _)]
  rw [real_inner_self_eq_norm_sq, hn] at h
  simpa using h

/-! ### Non-vacuity: fair coin flips -/

/-- The fair coin. -/
noncomputable abbrev coin : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

/-- I.i.d. fair coin flips, as the coordinates of `ℕ → Bool`. -/
noncomputable abbrev flips : Measure (ℕ → Bool) := Measure.infinitePi fun _ => coin

theorem flips_real_eval_zero (b : Bool) :
    flips.real ((fun ω : ℕ → Bool => ω 0) ⁻¹' {b}) = 1 / 2 := by
  rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton b),
    Measure.infinitePi_map_eval, ← measureReal_def]
  cases b
  · rw [bernoulliMeasure_real_apply _ (measurableSet_singleton false)]
    simp [unitInterval.coe_symm_eq]
    norm_num
  · rw [bernoulliMeasure_real_apply _ (measurableSet_singleton true)]
    simp

theorem identDistrib_flips (k : ℕ) :
    IdentDistrib (fun ω : ℕ → Bool => ω k) (fun ω => ω 0) flips flips :=
  ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

theorem iIndepFun_flips : iIndepFun (fun k (ω : ℕ → Bool) => ω k) flips :=
  iIndepFun_infinitePi (X := fun _ b => b) fun _ => measurable_id

instance : IsProbabilityMeasure (chiSquareMeasure 1) :=
  isProbabilityMeasure_chiSquareMeasure one_pos

theorem hasLaw_id_chiSquare_card_bool :
    HasLaw (id : ℝ → ℝ) (chiSquareMeasure (Fintype.card Bool - 1)) (chiSquareMeasure 1) :=
  HasLaw.id

/-- **Pearson's theorem for a fair coin**: all hypotheses hold, and the statistic converges to
`χ²₁`. -/
example :
    TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun _ : Bool => (1 / 2 : ℝ))
        (cellCount (fun k (ω : ℕ → Bool) => ω k) n ω))
      atTop id (fun _ => flips) (chiSquareMeasure 1) :=
  tendstoInDistribution_pearsonStatistic flips_real_eval_zero (fun _ => by norm_num)
    iIndepFun_flips identDistrib_flips (by simp) hasLaw_id_chiSquare_card_bool

/-- **The fitted theorem with no free parameters** (`F = Fin 0 → ℝ`, `s = 0`): the estimator,
Jacobian and linearization are all `0`, the efficiency hypothesis holds trivially, and the
theorem recovers the `χ²₁` limit for the fair coin. -/
example :
    TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun _ : Bool => (1 / 2 : ℝ))
        (cellCount (fun k (ω : ℕ → Bool) => ω k) n ω))
      atTop id (fun _ => flips) (chiSquareMeasure 1) := by
  have hZ : HasLaw (id : ℝ → ℝ) (chiSquareMeasure (Fintype.card Bool - 1 -
      finrank ℝ (LinearMap.range (0 : (Fin 0 → ℝ) →L[ℝ] EuclideanSpace ℝ Bool).toLinearMap)))
      (chiSquareMeasure 1) := by
    have h0 : finrank ℝ (LinearMap.range
        (0 : (Fin 0 → ℝ) →L[ℝ] EuclideanSpace ℝ Bool).toLinearMap) = 0 := by
      simp
    rw [h0]
    exact HasLaw.id
  have hθ : TendstoInMeasure flips (fun (n : ℕ) (ω : ℕ → Bool) =>
      √n • ((0 : Fin 0 → ℝ) - 0) - (0 : EuclideanSpace ℝ Bool →L[ℝ] (Fin 0 → ℝ))
        (pearsonResidual n (fun _ : Bool => (1 / 2 : ℝ))
          (cellCount (fun k (ω : ℕ → Bool) => ω k) n ω))) atTop 0 := by
    simp only [sub_self, smul_zero, zero_apply]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_const_nhds)
  exact tendstoInDistribution_pearsonStatistic_fitted (θhat := fun _ _ => 0)
    (pθ := fun (_ : Fin 0 → ℝ) (_ : Bool) => (1 / 2 : ℝ)) (θ₀ := 0) (D := 0) (J := 0) (L := 0)
    flips_real_eval_zero (fun _ => by norm_num) iIndepFun_flips identDistrib_flips
    (fun _ _ => by norm_num) (fun _ => by norm_num) measurable_const (hasFDerivAt_const _ _)
    (fun _ _ => by simp) (fun _ => by simp) (fun _ => aemeasurable_const) hθ (by simp) hZ

/-! ### Boundary: a zero-probability cell -/

/-- With `p = (1, 0)` every observation lands in the first cell; the second cell contributes
`0 / 0 = 0`, so the statistic is identically `0`. -/
theorem pearsonStatistic_degenerate (n : ℕ) :
    pearsonStatistic n (fun b : Bool => if b then 1 else 0)
      (cellCount (fun _ (_ : Unit) => true) n ()) = 0 := by
  simp [pearsonStatistic, cellCount]

/-- **The positivity hypothesis cannot be dropped.** For `p = (1, 0)` all hypotheses of
`tendstoInDistribution_pearsonStatistic` except `0 < pᵢ` hold, and the statistic does not
converge to `χ²_{k-1} = χ²₁`: it is identically `0`, and `χ²₁` has no atom at `0`. -/
example :
    ¬ TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : Unit) => true) n ω))
      atTop id (fun _ => Measure.dirac ()) (chiSquareMeasure 1) := by
  intro h
  have h0 : TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : Unit) => true) n ω))
      atTop (fun _ : Unit => (0 : ℝ)) (fun _ => Measure.dirac ()) (Measure.dirac ()) := by
    have hfun : (fun n (ω : Unit) => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : Unit) => true) n ω)) = fun _ _ => (0 : ℝ) := by
      ext n ω
      exact pearsonStatistic_degenerate n
    rw [hfun]
    exact tendstoInDistribution_const aemeasurable_const
  have heq := tendstoInDistribution_unique _ h h0
  have h1 : chiSquareMeasure 1 {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  rw [Measure.map_id] at heq
  rw [heq] at h1
  simp at h1

end PearsonTest
