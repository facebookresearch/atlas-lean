/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

/-!
# Continuum-of-alleles mutation-selection model

The haploid continuum-of-alleles model with Gaussian stabilizing selection
`w(x) = exp(-x² / (2 Vₛ))` and Gaussian incremental mutation: each generation, selection
reweights the allelic-effect distribution `ν` to `ν_w = w ν / ∫ w dν`, then mutation
replaces an allele `x` by `x + ξ` with probability `μ`, where `ξ ~ N(0, γ²)`. On
probability measures the one-generation map is
`T ν = (1 - μ) ν_w + μ (ν_w ∗ N(0, γ²))`.

## Main results

* `Params.isProbabilityMeasure_step`: `T` maps probability measures to probability
  measures, with `Params.stepPM` the bundled form.
* `Params.memLp_id_step`: `T ν` has finite second moment for every probability measure
  `ν`, since Gaussian selection gives moments of every order.
* `Params.variance_step`: the variance recursion `Var (T ν) = Var ν_w + μ γ²`.
* `Params.integral_id_step_eq_zero_of_map_neg`: a symmetric initial law keeps mean zero.

## References

* M. Kimura, "A stochastic model concerning the maintenance of genetic variability in
  quantitative characters", *Proceedings of the National Academy of Sciences* 54 (1965),
  731–736.
* D. Waxman, "Numerical and exact solutions for continuum of alleles models", *Journal
  of Mathematical Biology* 46 (2003), 225–240.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Nat

namespace MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection

/-- Parameters of the haploid continuum-of-alleles model: Gaussian stabilizing selection of
width `Vs`, mutation probability `mu`, Gaussian mutational effects of standard deviation
`gamma`. -/
structure Params where
  Vs : ℝ
  mu : ℝ
  gamma : ℝ
  Vs_pos : 0 < Vs
  mu_pos : 0 < mu
  mu_lt_one : mu < 1
  gamma_pos : 0 < gamma

namespace Params

variable (P : Params)

/-- Log-fitness `-x² / (2 Vs)`. -/
noncomputable def logFitness (x : ℝ) : ℝ := -x ^ 2 / (2 * P.Vs)

/-- Gaussian stabilizing fitness `w(x) = exp(-x² / (2 Vs))`. -/
noncomputable def fitness (x : ℝ) : ℝ := Real.exp (P.logFitness x)

/-- Mutational variance `γ²`. -/
noncomputable def mutVar : ℝ≥0 := ⟨P.gamma ^ 2, sq_nonneg _⟩

/-- Law of a mutational increment, `N(0, γ²)`. -/
noncomputable def mutationLaw : Measure ℝ := gaussianReal 0 P.mutVar

instance isProbabilityMeasure_mutationLaw : IsProbabilityMeasure P.mutationLaw := by
  unfold mutationLaw; infer_instance

/-- Selection: `ν_w = w ν / ∫ w dν`. -/
noncomputable def select (ν : Measure ℝ) : Measure ℝ := ν.tilted P.logFitness

/-- Mutation: `(1 - μ) ρ + μ (ρ ∗ N(0, γ²))`. -/
noncomputable def mutate (ρ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - P.mu) • ρ + ENNReal.ofReal P.mu • (ρ ∗ P.mutationLaw)

/-- One generation, selection then mutation: `T ν = (1-μ) ν_w + μ (ν_w ∗ N(0, γ²))`. -/
noncomputable def step (ν : Measure ℝ) : Measure ℝ := P.mutate (P.select ν)

theorem fitness_eq (x : ℝ) : P.fitness x = Real.exp (-x ^ 2 / (2 * P.Vs)) := rfl

theorem select_eq_withDensity (ν : Measure ℝ) :
    P.select ν =
      ν.withDensity (fun x => ENNReal.ofReal (P.fitness x / ∫ y, P.fitness y ∂ν)) := rfl

theorem step_eq (ν : Measure ℝ) :
    P.step ν = ENNReal.ofReal (1 - P.mu) • P.select ν +
      ENNReal.ofReal P.mu • (P.select ν ∗ gaussianReal 0 ⟨P.gamma ^ 2, sq_nonneg _⟩) := rfl

lemma continuous_fitness : Continuous P.fitness := by
  unfold fitness logFitness; fun_prop

lemma fitness_pos (x : ℝ) : 0 < P.fitness x := Real.exp_pos _

lemma fitness_le_one (x : ℝ) : P.fitness x ≤ 1 := by
  unfold fitness logFitness
  rw [Real.exp_le_one_iff]
  have := P.Vs_pos
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x]) (by linarith)

/-- `x^(2k) w(x) ≤ k! (2 Vs)^k`. -/
lemma pow_two_mul_fitness_le (k : ℕ) (x : ℝ) :
    x ^ (2 * k) * P.fitness x ≤ (k ! : ℝ) * (2 * P.Vs) ^ k := by
  have ha : 0 < 2 * P.Vs := by linarith [P.Vs_pos]
  have hy : 0 ≤ x ^ 2 / (2 * P.Vs) := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hy k
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hf : P.fitness x * Real.exp (x ^ 2 / (2 * P.Vs)) = 1 := by
    unfold fitness logFitness
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have h2 : x ^ (2 * k) = (x ^ 2 / (2 * P.Vs)) ^ k * (2 * P.Vs) ^ k := by
    rw [div_pow, div_mul_cancel₀ _ (pow_pos ha k).ne', pow_mul]
  rw [div_le_iff₀ hk] at h1
  have hw := P.fitness_pos x
  calc x ^ (2 * k) * P.fitness x
      = (x ^ 2 / (2 * P.Vs)) ^ k * P.fitness x * (2 * P.Vs) ^ k := by rw [h2]; ring
    _ ≤ (Real.exp (x ^ 2 / (2 * P.Vs)) * k !) * P.fitness x * (2 * P.Vs) ^ k := by gcongr
    _ = (k ! : ℝ) * (2 * P.Vs) ^ k := by
        rw [show Real.exp (x ^ 2 / (2 * P.Vs)) * k ! * P.fitness x * (2 * P.Vs) ^ k =
          (P.fitness x * Real.exp (x ^ 2 / (2 * P.Vs))) * k ! * (2 * P.Vs) ^ k by ring, hf,
          one_mul]

lemma abs_pow_mul_fitness_le (k : ℕ) (x : ℝ) :
    |x ^ k| * P.fitness x ≤ 1 + (k ! : ℝ) * (2 * P.Vs) ^ k := by
  have hw := P.fitness_pos x
  have hb : |x ^ k| ≤ 1 + x ^ (2 * k) := by
    rw [abs_pow]
    rcases le_total |x| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg x) h (n := k)
      have : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; positivity
      linarith
    · have h3 : |x| ^ k ≤ |x| ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      have : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, pow_mul, sq_abs]
      linarith
  calc |x ^ k| * P.fitness x ≤ (1 + x ^ (2 * k)) * P.fitness x := by gcongr
    _ = P.fitness x + x ^ (2 * k) * P.fitness x := by ring
    _ ≤ 1 + (k ! : ℝ) * (2 * P.Vs) ^ k := add_le_add (P.fitness_le_one x)
        (P.pow_two_mul_fitness_le k x)

lemma integrable_exp_logFitness (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun x => Real.exp (P.logFitness x)) ν := by
  refine Integrable.of_bound P.continuous_fitness.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
  calc ‖Real.exp (P.logFitness x)‖ = P.fitness x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), fitness]
    _ ≤ 1 := P.fitness_le_one x

theorem integral_fitness_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    0 < ∫ x, P.fitness x ∂ν :=
  integral_exp_pos (P.integrable_exp_logFitness ν)

theorem isProbabilityMeasure_select (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (P.select ν) :=
  isProbabilityMeasure_tilted (P.integrable_exp_logFitness ν)

theorem isProbabilityMeasure_mutate (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (P.mutate ρ) := by
  constructor
  simp only [mutate, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [P.mu_lt_one]) P.mu_pos.le]
  simp

theorem isProbabilityMeasure_step (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (P.step ν) := by
  have := P.isProbabilityMeasure_select ν
  exact P.isProbabilityMeasure_mutate _

/-- The generation map on probability measures. -/
noncomputable def stepPM (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨P.step ν, P.isProbabilityMeasure_step ν⟩

theorem integrable_pow_select (ν : Measure ℝ) [IsFiniteMeasure ν] (k : ℕ) :
    Integrable (fun x => x ^ k) (P.select ν) := by
  rw [select, integrable_tilted_iff (P.integrable_exp_logFitness ν)]
  refine Integrable.of_bound
    ((P.continuous_fitness.smul (continuous_pow k)).aestronglyMeasurable) (1 + (k ! : ℝ) * (2 * P.Vs) ^ k)
    (ae_of_all _ fun x => ?_)
  rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_comm]
  exact P.abs_pow_mul_fitness_le k x

/-! Moments of the mutation step. -/

lemma integrable_mutationLaw_id : Integrable (fun y : ℝ => y) P.mutationLaw :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_mutationLaw_sq : Integrable (fun y : ℝ => y ^ 2) P.mutationLaw :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp (memLp_id_gaussianReal 2)

lemma integral_mutationLaw_id : ∫ y, y ∂P.mutationLaw = 0 := integral_id_gaussianReal

lemma integral_mutationLaw_sq : ∫ y, y ^ 2 ∂P.mutationLaw = P.gamma ^ 2 := by
  have h := variance_eq_sub (μ := P.mutationLaw) (memLp_id_gaussianReal 2)
  rw [show Var[id; P.mutationLaw] = P.gamma ^ 2 from variance_id_gaussianReal] at h
  simp only [id, Pi.pow_apply] at h
  rw [show (∫ y, y ∂P.mutationLaw) = 0 from integral_mutationLaw_id P] at h
  have : (∫ x, (id ^ 2 : ℝ → ℝ) x ∂P.mutationLaw) = ∫ y, y ^ 2 ∂P.mutationLaw := rfl
  linarith [h]

lemma integrable_conv_id (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h1 : Integrable id ρ) :
    Integrable (fun x : ℝ => x) (ρ ∗ P.mutationLaw) := by
  unfold Measure.conv
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  exact (h1.comp_fst _).add (P.integrable_mutationLaw_id.comp_snd ρ)

lemma integrable_conv_sq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h2 : MemLp id 2 ρ) :
    Integrable (fun x : ℝ => x ^ 2) (ρ ∗ P.mutationLaw) := by
  have h1 : Integrable (fun x : ℝ => x) ρ := h2.integrable one_le_two
  have hsq : Integrable (fun x : ℝ => x ^ 2) ρ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp h2
  unfold Measure.conv
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have := ((hsq.comp_fst P.mutationLaw).add
    ((h1.mul_prod P.integrable_mutationLaw_id).const_mul 2)).add
    (P.integrable_mutationLaw_sq.comp_snd ρ)
  refine this.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp, Pi.add_apply]
  ring

lemma integral_conv_id (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h1 : Integrable id ρ) :
    ∫ x, x ∂(ρ ∗ P.mutationLaw) = ∫ x, x ∂ρ := by
  rw [integral_conv (P.integrable_conv_id ρ h1)]
  congr 1; funext x
  rw [integral_add (integrable_const x) P.integrable_mutationLaw_id, integral_const,
    P.integral_mutationLaw_id]
  simp

lemma integral_conv_sq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h2 : MemLp id 2 ρ) :
    ∫ x, x ^ 2 ∂(ρ ∗ P.mutationLaw) = ∫ x, x ^ 2 ∂ρ + P.gamma ^ 2 := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) ρ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp h2
  rw [integral_conv (P.integrable_conv_sq ρ h2)]
  have hin : ∀ x : ℝ, ∫ y, (x + y) ^ 2 ∂P.mutationLaw = x ^ 2 + P.gamma ^ 2 := by
    intro x
    have e : (fun y : ℝ => (x + y) ^ 2) =
        fun y => (x ^ 2 + 2 * x * y) + y ^ 2 := by funext y; ring
    have i1 : Integrable (fun y : ℝ => 2 * x * y) P.mutationLaw :=
      P.integrable_mutationLaw_id.const_mul _
    rw [e, integral_add (f := fun y => x ^ 2 + 2 * x * y) (g := fun y => y ^ 2)
      ((integrable_const _).add i1) P.integrable_mutationLaw_sq,
      integral_add (f := fun _ => x ^ 2) (g := fun y => 2 * x * y) (integrable_const _) i1,
      integral_const, integral_const_mul,
      P.integral_mutationLaw_id, P.integral_mutationLaw_sq]
    simp
  simp_rw [hin]
  rw [integral_add hsq (integrable_const _), integral_const]
  simp

theorem integral_id_mutate (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h1 : Integrable id ρ) :
    ∫ x, x ∂(P.mutate ρ) = ∫ x, x ∂ρ := by
  have hc := P.integrable_conv_id ρ h1
  have h1' : Integrable (fun x : ℝ => x) ρ := h1
  unfold mutate
  rw [integral_add_measure (h1'.smul_measure (by simp)) (hc.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, P.integral_conv_id ρ h1,
    ENNReal.toReal_ofReal (by linarith [P.mu_lt_one]), ENNReal.toReal_ofReal P.mu_pos.le]
  simp only [smul_eq_mul]; ring

theorem integral_sq_mutate (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h2 : MemLp id 2 ρ) :
    ∫ x, x ^ 2 ∂(P.mutate ρ) = ∫ x, x ^ 2 ∂ρ + P.mu * P.gamma ^ 2 := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) ρ :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp h2
  have hc := P.integrable_conv_sq ρ h2
  unfold mutate
  rw [integral_add_measure (hsq.smul_measure (by simp)) (hc.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, P.integral_conv_sq ρ h2,
    ENNReal.toReal_ofReal (by linarith [P.mu_lt_one]), ENNReal.toReal_ofReal P.mu_pos.le]
  simp only [smul_eq_mul]; ring

theorem memLp_id_select (ν : Measure ℝ) [IsProbabilityMeasure ν] : MemLp id 2 (P.select ν) := by
  have := P.isProbabilityMeasure_select ν
  exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr (P.integrable_pow_select ν 2)

theorem memLp_id_step (ν : Measure ℝ) [IsProbabilityMeasure ν] : MemLp id 2 (P.step ν) := by
  have := P.isProbabilityMeasure_select ν
  have := P.isProbabilityMeasure_step ν
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr ?_
  have h2 := P.memLp_id_select ν
  have hsq : Integrable (fun x : ℝ => x ^ 2) (P.select ν) := P.integrable_pow_select ν 2
  exact (hsq.smul_measure (by simp)).add_measure
    ((P.integrable_conv_sq _ h2).smul_measure (by simp))

theorem integral_id_select (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ x, x ∂(P.select ν) = (∫ x, x * P.fitness x ∂ν) / ∫ x, P.fitness x ∂ν := by
  rw [select, integral_tilted, ← integral_div]
  congr 1; funext x
  simp only [smul_eq_mul, fitness]; ring

theorem integral_sq_select (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ x, x ^ 2 ∂(P.select ν) = (∫ x, x ^ 2 * P.fitness x ∂ν) / ∫ x, P.fitness x ∂ν := by
  rw [select, integral_tilted, ← integral_div]
  congr 1; funext x
  simp only [smul_eq_mul, fitness]; ring

theorem integral_id_step (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ x, x ∂(P.step ν) = ∫ x, x ∂(P.select ν) := by
  have := P.isProbabilityMeasure_select ν
  exact P.integral_id_mutate _ ((P.memLp_id_select ν).integrable one_le_two)

theorem integral_sq_step (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ x, x ^ 2 ∂(P.step ν) = ∫ x, x ^ 2 ∂(P.select ν) + P.mu * P.gamma ^ 2 := by
  have := P.isProbabilityMeasure_select ν
  exact P.integral_sq_mutate _ (P.memLp_id_select ν)

theorem variance_step (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Var[id; P.step ν] = Var[id; P.select ν] + P.mu * P.gamma ^ 2 := by
  have := P.isProbabilityMeasure_select ν
  have := P.isProbabilityMeasure_step ν
  rw [variance_eq_sub (P.memLp_id_step ν), variance_eq_sub (P.memLp_id_select ν)]
  have e1 := P.integral_id_step ν
  have e2 := P.integral_sq_step ν
  simp only [id, Pi.pow_apply] at e1 e2 ⊢
  change (∫ x, x ^ 2 ∂P.step ν) - (∫ x, x ∂P.step ν) ^ 2 =
    (∫ x, x ^ 2 ∂P.select ν) - (∫ x, x ∂P.select ν) ^ 2 + P.mu * P.gamma ^ 2
  rw [e1, e2]; ring

theorem integral_id_step_eq_zero_of_map_neg (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsymm : ν.map (fun x => -x) = ν) : ∫ x, x ∂(P.step ν) = 0 := by
  rw [P.integral_id_step, P.integral_id_select]
  have hg : Continuous fun x => x * P.fitness x := continuous_id.mul P.continuous_fitness
  have hw : ∀ x, P.fitness (-x) = P.fitness x := by
    intro x; simp [fitness, logFitness]
  have h : ∫ x, x * P.fitness x ∂ν = -∫ x, x * P.fitness x ∂ν := by
    conv_lhs => rw [← hsymm]
    rw [integral_map measurable_neg.aemeasurable hg.aestronglyMeasurable, ← integral_neg]
    simp [hw]
  have h0 : ∫ x, x * P.fitness x ∂ν = 0 := by linarith
  rw [h0, zero_div]

end Params

end MathlibExt.Biology.PopulationGenetics.Classical.QuantMutationSelection
