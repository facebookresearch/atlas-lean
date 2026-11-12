/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GoodnessOfFit.Pearson
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Pearson's chi-square goodness-of-fit asymptotics

* Concrete values of `cellCount`, `pearsonStatistic` and `pearsonResidual`.
* One cell: the statistic is identically `0` (why `k ≥ 2` is assumed).
* The limit of the residuals is singular: zero variance in the direction `√p`.
* Non-vacuity: fair coin flips on `ℕ → Bool` satisfy every hypothesis of Pearson's theorem,
  giving the `χ²₁` limit; the fitted theorem with a zero-dimensional parameter space recovers it.
* One fitted parameter: the model `(1/3 + sin θ / 6, 1/3 - sin θ / 6, 1/3)` with uniform
  observations and the oracle efficient estimator `θ̂ = n^{-1/2} L(Rₙ)` gives `χ²_{3-1-1} = χ²₁`
  (nonzero tangent space, degree-of-freedom drop).
* Boundary: with a zero-probability cell (`p = (1, 0)`) every other hypothesis holds, the
  statistic is identically `0`, and it does not converge to `χ²₁`, so the positivity hypothesis
  cannot be dropped.
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
    (fun _ _ => by norm_num) (Eventually.of_forall fun _ => by norm_num) measurable_const
    (hasFDerivAt_const _ _)
    (fun _ _ => by simp) (fun _ => by simp) (fun _ => aemeasurable_const) hθ (by simp) hZ

/-! ### A genuine one-parameter model (`s = 1`) -/

/-- The direction of the one-parameter model. -/
noncomputable abbrev dir3 : Fin 3 → ℝ := ![1 / 6, -1 / 6, 0]

/-- The model `p(θ) = (1/3 + sin θ / 6, 1/3 - sin θ / 6, 1/3)` on `ℝ`, with `θ₀ = 0`. -/
noncomputable abbrev model3 (θ : ℝ) : Fin 3 → ℝ := fun i => 1 / 3 + Real.sin θ * dir3 i

theorem model3_zero (i : Fin 3) : model3 0 i = 1 / 3 := by simp [model3]

theorem model3_nonneg (θ : ℝ) (i : Fin 3) : 0 ≤ model3 θ i := by
  have h1 := Real.neg_one_le_sin θ
  have h2 := Real.sin_le_one θ
  fin_cases i <;> simp [model3, dir3] <;> linarith

theorem model3_sum (θ : ℝ) : ∑ i, model3 θ i = 1 := by
  simp [model3, dir3, Fin.sum_univ_three]
  ring

theorem hasFDerivAt_model3 :
    HasFDerivAt model3 ((1 : ℝ →L[ℝ] ℝ).smulRight dir3) 0 := by
  have h : HasDerivAt model3 dir3 0 := by
    rw [hasDerivAt_pi]
    intro i
    simpa using ((Real.hasDerivAt_sin 0).mul_const (dir3 i)).const_add (1 / 3)
  exact h.hasFDerivAt

/-- The weighted tangent vector `(dir3 i / √(1/3))ᵢ`. -/
noncomputable abbrev jvec : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => dir3 i / √(1 / 3)

theorem jvec_ne_zero : jvec ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  simp [dir3] at this

/-- The weighted Jacobian `a ↦ a • jvec`. -/
noncomputable abbrev J3 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) := (1 : ℝ →L[ℝ] ℝ).smulRight jvec

/-- The efficient linearization `v ↦ ⟪jvec, v⟫ / ‖jvec‖²`. -/
noncomputable abbrev L3 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := (‖jvec‖ ^ 2)⁻¹ • innerSL ℝ jvec

theorem range_J3 : LinearMap.range J3.toLinearMap = ℝ ∙ jvec := by
  ext v
  simp [Submodule.mem_span_singleton, eq_comm]

theorem J3_L3 (v : EuclideanSpace ℝ (Fin 3)) :
    J3 (L3 v) = (LinearMap.range J3.toLinearMap).starProjection v := by
  simp only [range_J3, Submodule.starProjection_singleton]
  simp [div_eq_inv_mul]

/-- The uniform law on three cells. -/
noncomputable abbrev die : Measure (Fin 3) := uniformOn Set.univ

/-- I.i.d. uniform observations on three cells, as the coordinates of `ℕ → Fin 3`. -/
noncomputable abbrev rolls : Measure (ℕ → Fin 3) := Measure.infinitePi fun _ => die

theorem rolls_real_eval_zero (i : Fin 3) :
    rolls.real ((fun ω : ℕ → Fin 3 => ω 0) ⁻¹' {i}) = model3 0 i := by
  rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton i),
    Measure.infinitePi_map_eval, model3_zero, uniformOn_univ]
  simp

theorem identDistrib_rolls (k : ℕ) :
    IdentDistrib (fun ω : ℕ → Fin 3 => ω k) (fun ω => ω 0) rolls rolls :=
  ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩

theorem iIndepFun_rolls : iIndepFun (fun k (ω : ℕ → Fin 3) => ω k) rolls :=
  iIndepFun_infinitePi (X := fun _ i => i) fun _ => measurable_id

/-- The Pearson residuals at `θ₀ = 0` for the uniform observations. -/
noncomputable abbrev res3 (n : ℕ) (ω : ℕ → Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  pearsonResidual n (model3 0) (cellCount (fun k (ω : ℕ → Fin 3) => ω k) n ω)

/-- The oracle efficient estimator `θ̂ n = θ₀ + n^{-1/2} L(Rₙ)`: its linearization remainder
vanishes identically. -/
noncomputable abbrev oracle (n : ℕ) (ω : ℕ → Fin 3) : ℝ := (√(n : ℝ))⁻¹ * L3 (res3 n ω)

/-- **Pearson's theorem with one fitted parameter.** For the model `model3` (`k = 3`, `s = 1`)
and the oracle efficient estimator, the fitted statistic converges to `χ²_{3-1-1} = χ²₁`. This
runs the delta-method branch with a nonzero tangent space and the degree-of-freedom drop. -/
example :
    TendstoInDistribution
      (fun n ω => pearsonStatistic n (model3 (oracle n ω))
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
  exact tendstoInDistribution_pearsonStatistic_fitted_of_injective (θ₀ := 0)
    (D := (1 : ℝ →L[ℝ] ℝ).smulRight dir3) (J := J3) (L := L3)
    rolls_real_eval_zero hpos iIndepFun_rolls identDistrib_rolls model3_nonneg
    (Eventually.of_forall model3_sum) (by fun_prop) hasFDerivAt_model3
    (fun a i => by simp [model3_zero]; ring)
    (fun a b h => smul_left_injective ℝ jvec_ne_zero (by simpa using h)) J3_L3 hθm hθ
    (by simp) hZ

/-! ### Boundary: a zero-probability cell -/

/-- Observations that always land in the first cell, on `ℕ → Unit` under the product of Dirac
masses. -/
noncomputable abbrev point : Measure (ℕ → Unit) := Measure.infinitePi fun _ => Measure.dirac ()

/-- With `p = (1, 0)` every observation lands in the first cell; the second cell contributes
`0 / 0 = 0`, so the statistic is identically `0`. -/
theorem pearsonStatistic_degenerate (n : ℕ) (ω : ℕ → Unit) :
    pearsonStatistic n (fun b : Bool => if b then 1 else 0)
      (cellCount (fun _ (_ : ℕ → Unit) => true) n ω) = 0 := by
  simp [pearsonStatistic, cellCount]

/-- For `p = (1, 0)` and the constant observations, every hypothesis of
`tendstoInDistribution_pearsonStatistic` holds except positivity of `p`. -/
theorem degenerate_hypotheses :
    (∀ b, point.real ((fun _ : ℕ → Unit => true) ⁻¹' {b}) = if b then 1 else 0) ∧
    iIndepFun (fun (_ : ℕ) (_ : ℕ → Unit) => true) point ∧
    (∀ _ : ℕ, IdentDistrib (fun _ : ℕ → Unit => true) (fun _ : ℕ → Unit => true) point point) ∧
    2 ≤ Fintype.card Bool ∧ ¬ ∀ b : Bool, 0 < (if b then (1 : ℝ) else 0) := by
  refine ⟨fun b => ?_, iIndepFun_infinitePi (X := fun _ (_ : Unit) => true)
    fun _ => measurable_const, fun _ => IdentDistrib.refl aemeasurable_const, by simp,
    fun h => by simpa using h false⟩
  cases b <;> simp

/-- **The positivity hypothesis cannot be dropped.** For `p = (1, 0)` all other hypotheses of
`tendstoInDistribution_pearsonStatistic` hold (`degenerate_hypotheses`), and the statistic does
not converge to `χ²_{k-1} = χ²₁`: it is identically `0`, and `χ²₁` has no atom at `0`. -/
example :
    ¬ TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω))
      atTop id (fun _ => point) (chiSquareMeasure 1) := by
  intro h
  have h0 : TendstoInDistribution
      (fun n ω => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω))
      atTop (fun _ : ℕ → Unit => (0 : ℝ)) (fun _ => point) point := by
    have hfun : (fun n (ω : ℕ → Unit) => pearsonStatistic n (fun b : Bool => if b then 1 else 0)
        (cellCount (fun _ (_ : ℕ → Unit) => true) n ω)) = fun _ _ => (0 : ℝ) := by
      ext n ω
      exact pearsonStatistic_degenerate n ω
    rw [hfun]
    exact tendstoInDistribution_const aemeasurable_const
  have heq := tendstoInDistribution_unique _ h h0
  have h1 : chiSquareMeasure 1 {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  rw [Measure.map_id] at heq
  rw [heq] at h1
  simp at h1

end PearsonTest
