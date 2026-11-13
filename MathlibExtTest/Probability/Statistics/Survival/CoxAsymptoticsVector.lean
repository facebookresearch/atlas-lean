/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxAsymptoticsVector
public import MathlibExtTest.Probability.Statistics.Survival.CoxAsymptotics

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real Matrix
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptotics
open MathlibExt.Probability.Statistics.CoxAsymptoticsVector
open MathlibExtTest.Probability.Statistics.CoxAsymptotics

namespace MathlibExtTest.Probability.Statistics.CoxAsymptoticsVector

/-! ### A two-covariate example computed from the definitions

Three subjects at times `1, 2, 3`, all with events, covariate vectors `(1, 0)`, `(0, 1)`,
`(0, 0)`. At `β = 0` every weight is `exp 0 = 1`, so the risk-set means are plain averages:
`(1/3, 1/3)` over `{0, 1, 2}`, `(0, 1/2)` over `{1, 2}`, `(0, 0)` over `{2}`. The score vector is
`(2/3, -1/3) + (0, 1/2) + 0 = (2/3, 1/6)`; the information matrix is the sum of the risk-set
covariances `[[2/9, -1/9], [-1/9, 2/9]] + [[0, 0], [0, 1/4]] + 0`. -/

/-- Observed times. -/
noncomputable def T₃ : Fin 3 → ℝ := ![1, 2, 3]

/-- All three subjects have events. -/
def δ₃ : Fin 3 → Bool := ![true, true, true]

/-- Covariate vectors. -/
noncomputable def x₃ : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![0, 0]]

theorem riskSet_T₃_zero : riskSet T₃ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₃]

theorem riskSet_T₃_one : riskSet T₃ 1 = {1, 2} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  fin_cases l <;> norm_num [T₃]

theorem riskSet_T₃_two : riskSet T₃ 2 = {2} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_cases l <;> norm_num [T₃]

theorem filter_δ₃ : univ.filter (fun i => δ₃ i = true) = univ := by decide

/-- The score vector at `β = 0`, computed from the definitions. -/
theorem coxGradient_x₃ : coxGradient T₃ δ₃ x₃ 0 = ![2 / 3, 1 / 6] := by
  funext j
  rw [coxGradient, filter_δ₃]
  simp only [Finset.sum_apply, Fin.sum_univ_three, Pi.sub_apply, riskMeanVec_apply,
    riskSet_T₃_zero, riskSet_T₃_one, riskSet_T₃_two, zero_dotProduct, exp_zero, mul_one,
    sum_pair (show (1 : Fin 3) ≠ 2 by decide), sum_singleton]
  fin_cases j <;> norm_num [x₃]

/-- The limiting-information candidate: the information matrix of the example at `β = 0`. -/
noncomputable def Sigma₃ : Matrix (Fin 2) (Fin 2) ℝ := !![2 / 9, -1 / 9; -1 / 9, 17 / 36]

/-- The information matrix at `β = 0`, computed from the definitions. -/
theorem coxInfoMatrix_x₃ : coxInfoMatrix T₃ δ₃ x₃ 0 = Sigma₃ := by
  ext j k
  rw [coxInfoMatrix, filter_δ₃]
  simp only [Matrix.sum_apply, Fin.sum_univ_three, riskCov, of_apply, riskMeanVec_apply,
    riskSet_T₃_zero, riskSet_T₃_one, riskSet_T₃_two, zero_dotProduct, exp_zero, mul_one,
    sum_pair (show (1 : Fin 3) ≠ 2 by decide), sum_singleton]
  fin_cases j <;> fin_cases k <;> norm_num [x₃, Sigma₃]

/-- The Jacobian of the score vector at `0` is `-Sigma₃`. -/
example : HasFDerivAt (coxGradient T₃ δ₃ x₃) (-mulVecCLM Sigma₃) 0 :=
  coxInfoMatrix_x₃ ▸ hasFDerivAt_coxGradient T₃ δ₃ x₃ 0

theorem posDef_Sigma₃ : Sigma₃.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun y hy => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Sigma₃]
  · have hy' : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, Sigma₃, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    rcases hy' with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (y 0 - y 1 / 2), sq_nonneg (y 1),
        sq_nonneg (y 0 - 2 * y 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (y 0 - y 1 / 2)]

/-- The limit covariance `Sigma₃⁻¹`, computed by inverting `Sigma₃`. -/
theorem inv_Sigma₃ : Sigma₃⁻¹ = !![51 / 10, 6 / 5; 6 / 5, 12 / 5] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Sigma₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- One Newton step from `0`: `Sigma₃⁻¹ U(0) = (18/5, 6/5)`. -/
example : Sigma₃⁻¹ *ᵥ coxGradient T₃ δ₃ x₃ 0 = ![18 / 5, 6 / 5] := by
  rw [inv_Sigma₃, coxGradient_x₃]
  funext j
  fin_cases j <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two]

/-- **Limit law for this information matrix.** If the score limit is `N(0, Sigma₃)`, the
estimator limit `Sigma₃⁻¹ Z` is `N(0, Sigma₃⁻¹)` with the explicit covariance above. -/
example : HasLaw (fun y => toEuclideanLin Sigma₃⁻¹ y)
    (multivariateGaussian 0 !![51 / 10, 6 / 5; 6 / 5, 12 / 5])
    (multivariateGaussian 0 Sigma₃) := by
  rw [← inv_Sigma₃]
  exact hasLaw_toEuclideanLin_inv_multivariateGaussian posDef_Sigma₃ HasLaw.id

/-! ### A singular information matrix: no normal limit is claimed

Two subjects at times `1, 2`, both with events, covariates `(1, 0)` and `(0, 1)`. At `β = 0` the
only nontrivial risk set is `{0, 1}`, whose covariance is `[[1/4, -1/4], [-1/4, 1/4]]`: singular
in the direction `(1, 1)`. Such a matrix is not positive definite, so it cannot be the limit
information of `AndersenGillVector`, and the normality theorem says nothing. -/

/-- Observed times. -/
noncomputable def T₄ : Fin 2 → ℝ := ![1, 2]

/-- Both subjects have events. -/
def δ₄ : Fin 2 → Bool := ![true, true]

/-- Covariate vectors. -/
noncomputable def x₄ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

theorem riskSet_T₄_zero : riskSet T₄ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₄]

theorem riskSet_T₄_one : riskSet T₄ 1 = {1} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_cases l <;> norm_num [T₄]

theorem filter_δ₄ : univ.filter (fun i => δ₄ i = true) = univ := by decide

/-- The singular information matrix at `β = 0`, computed from the definitions. -/
theorem coxInfoMatrix_x₄ : coxInfoMatrix T₄ δ₄ x₄ 0 = !![1 / 4, -1 / 4; -1 / 4, 1 / 4] := by
  ext j k
  rw [coxInfoMatrix, filter_δ₄]
  simp only [Matrix.sum_apply, Fin.sum_univ_two, riskCov, of_apply, riskMeanVec_apply,
    riskSet_T₄_zero, riskSet_T₄_one, zero_dotProduct, exp_zero, mul_one, sum_singleton]
  fin_cases j <;> fin_cases k <;> norm_num [x₄]

theorem det_coxInfoMatrix_x₄ : (coxInfoMatrix T₄ δ₄ x₄ 0).det = 0 := by
  rw [coxInfoMatrix_x₄, det_fin_two_of]
  norm_num

theorem not_posDef_coxInfoMatrix_x₄ : ¬ (coxInfoMatrix T₄ δ₄ x₄ 0).PosDef := fun h => by
  have := h.dotProduct_mulVec_pos (x := ![1, 1]) (by simp [funext_iff, Fin.forall_fin_two])
  rw [coxInfoMatrix_x₄] at this
  norm_num [dotProduct, mulVec, Fin.sum_univ_two] at this

/-- The vector Andersen–Gill conditions cannot hold with this singular matrix as the limiting
information at `β₀`: normality is not claimed. -/
example {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
    {x : (n : ℕ) → Ω → Fin n → Fin 2 → ℝ} {β₀ : Fin 2 → ℝ} {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    {r : ℝ} : ¬ AndersenGillVector P P' T δ x β₀ Z (fun _ => coxInfoMatrix T₄ δ₄ x₄ 0) r :=
  fun h => not_posDef_coxInfoMatrix_x₄ h.info_posDef

/-- **Duplicated covariates make every information matrix singular.** With `xₗ = (zₗ, zₗ)`,
`Iₙ(b) (1, -1) = 0` for every sample and every `b`. -/
theorem coxInfoMatrix_dup_mulVec {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ)
    (b : Fin 2 → ℝ) : coxInfoMatrix T δ (fun l => ![z l, z l]) b *ᵥ ![1, -1] = 0 := by
  funext j
  simp only [mulVec, dotProduct, Fin.sum_univ_two, coxInfoMatrix, Matrix.sum_apply, riskCov,
    of_apply, riskMeanVec_apply]
  fin_cases j <;> simp

/-! ### `p = 1` reduces to the scalar theorem

The scalar Andersen–Gill hypotheses of `CoxAsymptotics` give the vector conditions for the
`1`-dimensional covariates `xᵢ = (zᵢ)`, with `info b = [[i (b 0)]]`; the vector consistency
theorem then gives back the scalar consistency theorem. -/

section ScalarReduction

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
  {z : (n : ℕ) → Ω → Fin n → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

private lemma eq_const_zero {α : Type*} (b : Fin 1 → α) : b = fun _ => b 0 :=
  funext fun j => by rw [Subsingleton.elim j 0]

/-- The scalar Andersen–Gill hypotheses imply the vector conditions at `p = 1`. -/
theorem andersenGillVector_of_scalar (hv : v ≠ 0)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    AndersenGillVector P P' T δ (fun n ω l (_ : Fin 1) => z n ω l) (fun _ : Fin 1 => β₀)
      (fun ω => WithLp.toLp 2 (fun _ : Fin 1 => Z ω))
      (fun b : Fin 1 → ℝ => Matrix.of fun (_ _ : Fin 1) => i (b 0)) r where
  score := by
    have hg : Continuous fun s : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => s) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
    have h := hscore.continuous_comp hg
    have heq : (fun (n : ℕ) ω ↦ WithLp.toLp 2 ((√(n : ℝ))⁻¹ •
        coxGradient (T n ω) (δ n ω) (fun l (_ : Fin 1) => z n ω l) (fun _ => β₀))) =
        fun n => (fun s : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => s)) ∘
          fun ω => coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ) := by
      funext n ω
      simp only [Function.comp, coxGradient_one]
      congr 1
      funext j
      simp [div_eq_inv_mul]
    rw [heq]
    exact h
  info_unif := by
    intro η hη
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hinfo η hη)
      (fun _ => zero_le) fun n => measure_mono ?_
    rintro ω ⟨b, hb, j, k, hjk⟩
    refine ⟨b 0, ?_, ?_⟩
    · have h := (dist_le_pi_dist b (fun _ => β₀) 0).trans (Metric.mem_closedBall.1 hb)
      rw [Real.dist_eq, abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rw [eq_const_zero b, coxInfoMatrix_one] at hjk
      simpa using hjk
  info_cont := fun _ _ => hi.comp (f := fun b : Fin 1 → ℝ => b 0) (continuous_apply 0).continuousAt
  info_posDef := by
    have hv' : (0 : ℝ) < v := by positivity
    have hd : (Matrix.of fun _ _ => i ((fun _ : Fin 1 => β₀) 0) : Matrix (Fin 1) (Fin 1) ℝ) =
        diagonal fun _ => (v : ℝ) := by
      ext a c
      fin_cases a; fin_cases c
      simp [hiv]
    rw [hd, posDef_diagonal_iff]
    exact fun _ => hv'
  radius_pos := hr

/-- **The scalar consistency theorem from the vector one.** Under the scalar hypotheses of
`tendstoInMeasure_coxMPLE`, the vector theorem `tendstoInMeasure_coxMPLE_vector` at `p = 1`
gives `βhat n → β₀` in probability. -/
theorem tendstoInMeasure_coxMPLE_of_vector (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) := by
  have hAG := andersenGillVector_of_scalar hv hscore hi hiv hinfo hr
  have hβv : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (T n ω) (δ n ω)
      (fun l (_ : Fin 1) => z n ω l)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (T n ω) (δ n ω) (fun l (_ : Fin 1) => z n ω l)) Set.univ
        (fun _ => βhat n ω) := by
    rintro n ω ⟨b, hb⟩
    have hs : ∃ s, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ s :=
      ⟨b 0, fun s _ => by
        have h := hb (Set.mem_univ (fun _ => s))
        rw [eq_const_zero b] at h
        exact h⟩
    have hmax := hβhat n ω hs
    intro c _
    have h := hmax (Set.mem_univ (c 0))
    rw [eq_const_zero c]
    exact h
  have h := tendstoInMeasure_coxMPLE_vector hAG hβv
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa [dist_pi_const] using h ε hε

end ScalarReduction

/-! ### Non-vacuity at `p = 1`: the balanced tied design

The balanced design of the scalar test file (`Tb`, `δb`, `zb`, limiting information `ibal`)
satisfies the scalar hypotheses, hence the vector conditions at `p = 1`. -/

/-- The vector Andersen–Gill conditions hold for the balanced design at `p = 1`. -/
theorem andersenGillVector_balanced :
    AndersenGillVector (Measure.dirac ()) (Measure.dirac ()) (fun n _ => Tb n)
      (fun n _ => δb n) (fun n _ l (_ : Fin 1) => zb n l) (fun _ : Fin 1 => (0 : ℝ))
      (fun _ => WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)))
      (fun b : Fin 1 → ℝ => Matrix.of fun (_ _ : Fin 1) => ibal (b 0)) 1 :=
  andersenGillVector_of_scalar (v := 1 / 4) (by norm_num) tendstoInDistribution_score_balanced
    continuous_ibal.continuousAt ibal_zero info_hyp_balanced one_pos

/-- The vector consistency theorem applies to the balanced design. -/
example (βhat : ℕ → Unit → Fin 1 → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (Tb n) (δb n)
      (fun l (_ : Fin 1) => zb n l)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (Tb n) (δb n) (fun l (_ : Fin 1) => zb n l)) Set.univ
        (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ()) βhat atTop (fun _ => fun _ => (0 : ℝ)) :=
  tendstoInMeasure_coxMPLE_vector andersenGillVector_balanced hβhat

/-- The vector limit theorem applies to the balanced design, whose score limit is `Z = 0`:
`√n βhat n ⟶ info(0)⁻¹ 0 = 0`. As in the scalar file, a design with a nondegenerate Gaussian
score limit is not constructed here. -/
example (βhat : ℕ → Unit → Fin 1 → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood (Tb n) (δb n)
      (fun l (_ : Fin 1) => zb n l)) Set.univ b) →
      IsMaxOn (logPartialLikelihood (Tb n) (δb n) (fun l (_ : Fin 1) => zb n l)) Set.univ
        (βhat n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ WithLp.toLp 2 (√(n : ℝ) • (βhat n ω - fun _ => 0)))
      atTop (fun _ => 0) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) := by
  have h := tendstoInDistribution_coxMPLE_vector andersenGillVector_balanced hβhat
    (fun _ => (measurable_from_top (f := βhat _)).aemeasurable)
  have h0 : (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) : EuclideanSpace ℝ (Fin 1)) = 0 := rfl
  simp only [h0, map_zero] at h
  exact h

#print axioms hasFDerivAt_riskMeanVec
#print axioms hasFDerivAt_coxGradient
#print axioms coxInfoMatrix_one
#print axioms antitone_coxGradient_dotProduct
#print axioms exists_pos_mul_sq_le_dotProduct_mulVec
#print axioms norm_coxGradient_sub_add_mulVec_le
#print axioms coxGradient_add_dotProduct_neg
#print axioms isMaxOn_of_coxGradient_eq_zero
#print axioms exists_isMaxOn_and_norm_sub_lt
#print axioms norm_sub_lt_of_isMaxOn
#print axioms norm_sqrt_smul_sub_sub_le
#print axioms hasLaw_toEuclideanLin_inv_multivariateGaussian
#print axioms tendsto_measure_not_coxGradient_eq_zero_and_norm_sub_lt
#print axioms tendsto_measure_not_exists_isMaxOn_vector
#print axioms tendstoInMeasure_coxMPLE_vector
#print axioms tendstoInDistribution_coxMPLE_vector
#print axioms tendstoInDistribution_coxMPLE_vector_gaussian
#print axioms tendstoInMeasure_coxInfoMatrix_coxMPLE_vector
#print axioms coxGradient_x₃
#print axioms coxInfoMatrix_x₃
#print axioms posDef_Sigma₃
#print axioms inv_Sigma₃
#print axioms not_posDef_coxInfoMatrix_x₄
#print axioms coxInfoMatrix_dup_mulVec
#print axioms andersenGillVector_of_scalar
#print axioms tendstoInMeasure_coxMPLE_of_vector
#print axioms andersenGillVector_balanced

end MathlibExtTest.Probability.Statistics.CoxAsymptoticsVector
