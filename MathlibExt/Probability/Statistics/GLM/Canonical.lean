/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr
public import MathlibExt.Analysis.Calculus.DotProductGradient
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Canonical logistic and Poisson generalized linear models

Observations are indexed by a finite type `ι`, coefficients by a finite type `κ`. A design matrix
`X : Matrix ι κ ℝ` and a fixed offset vector `o : ι → ℝ` (never optimized) give the linear
predictor `η(β) = X β + o` (`linearPredictor`). The responses `y : ι → ℝ` are fixed observed
values; every likelihood here is a deterministic function of `β`.

* **Bernoulli with logit link.** The mean is `μᵢ = σ(ηᵢ)` with Mathlib's `Real.sigmoid`. The log
  likelihood is `ℓ(β) = ∑ᵢ (yᵢ ηᵢ - log (1 + exp ηᵢ))` (`logisticLogLik`);
  `sigmoid_logLik_term` is the per-observation identity
  `y log σ(η) + (1 - y) log (1 - σ(η)) = y η - log (1 + exp η)`, valid for every real `y`.
* **Poisson with log link.** The mean is `exp ηᵢ` and the log likelihood, up to the constant
  `-∑ᵢ log yᵢ!`, is `∑ᵢ (yᵢ ηᵢ - exp ηᵢ)` (`poissonLogLik`).

For both models:

* `hasFDerivAt_logisticLogLik`, `hasFDerivAt_poissonLogLik`: the Fréchet derivative at `β` is
  `Real.dotL (Xᵀ (y - μ(β)))`, and the `hasGradientAt_*` corollaries state that `Xᵀ (y - μ(β))` is
  the gradient on `EuclideanSpace ℝ κ`.
* `deriv2_logisticLogLik_line`, `deriv2_poissonLogLik_line`: along `t ↦ β + t u` the second
  derivative at `0` is `-∑ᵢ wᵢ ((X u)ᵢ)²` with `wᵢ = σ(ηᵢ)(1 - σ(ηᵢ))`, resp. `wᵢ = exp ηᵢ`.
* `concaveOn_logisticLogLik`, `concaveOn_poissonLogLik`: concavity on all of `κ → ℝ`.
* `logisticLogLik_maximizer_unique`, `poissonLogLik_maximizer_unique`: if `β ↦ X β` is injective
  there is at most one maximizer. Existence is not claimed and can fail:
  `logisticLogLik_separation_not_isMaxOn` (complete separation) and
  `poissonLogLik_allZero_not_isMaxOn` (all-zero counts) have no maximizer, the first with an
  injective design (`separationDesign_mulVec_injective`).
* `logisticDeviance` and `logisticDeviance_nonneg` for binary responses.

## Response laws

The models are normalized: `σ(η) ∈ (0, 1)` (`unitInterval.sigmoid η`), so the Bernoulli response
law is `ProbabilityTheory.bernoulliMeasure 1 0 (unitInterval.sigmoid η)`, and the Poisson law is
`ProbabilityTheory.poissonMeasure ⟨exp η, (exp_pos η).le⟩`. Identifying the log likelihoods
above with the log density of the product of these laws is not done here.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM

open Finset Real Matrix

variable {ι κ : Type*} [Fintype κ]

/-- The linear predictor `η(β) = X β + o` of a generalized linear model with design `X` and a fixed
offset `o`. -/
def linearPredictor (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) : ι → ℝ :=
  X *ᵥ β + o

theorem linearPredictor_apply (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) (i : ι) :
    linearPredictor X o β i = (X *ᵥ β) i + o i := rfl

private lemma linearPredictor_combo (X : Matrix ι κ ℝ) (o : ι → ℝ) (β γ : κ → ℝ) {a b : ℝ}
    (hab : a + b = 1) (i : ι) :
    linearPredictor X o (a • β + b • γ) i =
      a * linearPredictor X o β i + b * linearPredictor X o γ i := by
  simp only [linearPredictor_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (o i) * hab.symm

private lemma linearPredictor_line (X : Matrix ι κ ℝ) (o : ι → ℝ) (β u : κ → ℝ) (t : ℝ)
    (i : ι) :
    linearPredictor X o (β + t • u) i = linearPredictor X o β i + t * (X *ᵥ u) i := by
  simp only [linearPredictor_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

variable [Fintype ι]

/-! ### A sum of scalar terms of the linear predictor -/

section Engine

variable (X : Matrix ι κ ℝ) (o : ι → ℝ) (f f' f'' : ι → ℝ → ℝ)

private lemma hasFDerivAt_sum_terms (hf : ∀ i x, HasDerivAt (f i) (f' i x) x) (β : κ → ℝ) :
    HasFDerivAt (fun β => ∑ i, f i (linearPredictor X o β i))
      (Real.dotL (X.transpose *ᵥ fun i => f' i (linearPredictor X o β i))) β := by
  have hη : ∀ i, HasFDerivAt (fun β => linearPredictor X o β i) (Real.dotL (X i)) β := by
    intro i
    have e : (fun β => linearPredictor X o β i) = fun β => β ⬝ᵥ X i + o i := by
      funext β
      simp [linearPredictor_apply, Matrix.mulVec, dotProduct_comm]
    rw [e]
    exact (Real.hasFDerivAt_dotProduct (X i) β).add_const (o i)
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hf i (linearPredictor X o β i)).comp_hasFDerivAt β (hη i)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    Real.dotL_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hasDerivAt_sum_terms_line (hf : ∀ i x, HasDerivAt (f i) (f' i x) x)
    (β u : κ → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ i, f i (linearPredictor X o (β + t • u) i))
      (∑ i, f' i (linearPredictor X o β i + t * (X *ᵥ u) i) * (X *ᵥ u) i) t := by
  simp only [linearPredictor_line]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hl : HasDerivAt (fun t => linearPredictor X o β i + t * (X *ᵥ u) i) ((X *ᵥ u) i) t := by
    simpa using (hasDerivAt_mul_const ((X *ᵥ u) i)).const_add (linearPredictor X o β i)
  exact (hf i _).comp t hl

private lemma deriv2_sum_terms_line (hf : ∀ i x, HasDerivAt (f i) (f' i x) x)
    (hf' : ∀ i x, HasDerivAt (f' i) (f'' i x) x) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => ∑ i, f i (linearPredictor X o (β + t • u) i)) 0 =
      ∑ i, f'' i (linearPredictor X o β i) * (X *ᵥ u) i ^ 2 := by
  have hd : deriv (fun t : ℝ => ∑ i, f i (linearPredictor X o (β + t • u) i)) =
      fun t => ∑ i, f' i (linearPredictor X o β i + t * (X *ᵥ u) i) * (X *ᵥ u) i :=
    funext fun t => (hasDerivAt_sum_terms_line X o f f' hf β u t).deriv
  have h2 : HasDerivAt
      (fun t => ∑ i, f' i (linearPredictor X o β i + t * (X *ᵥ u) i) * (X *ᵥ u) i)
      (∑ i, f'' i (linearPredictor X o β i) * (X *ᵥ u) i ^ 2) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hl : HasDerivAt (fun t => linearPredictor X o β i + t * (X *ᵥ u) i) ((X *ᵥ u) i) 0 := by
      simpa using (hasDerivAt_mul_const ((X *ᵥ u) i)).const_add (linearPredictor X o β i)
    have hc := ((hf' i (linearPredictor X o β i + 0 * (X *ᵥ u) i)).comp 0 hl).mul_const
      ((X *ᵥ u) i)
    convert hc using 1
    · simp
    · simp only [zero_mul, add_zero]
      ring
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd]
  exact h2.deriv

private lemma concaveOn_sum_terms (hc : ∀ i, ConcaveOn ℝ Set.univ (f i)) :
    ConcaveOn ℝ Set.univ (fun β => ∑ i, f i (linearPredictor X o β i)) := by
  refine ⟨convex_univ, fun β _ γ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [linearPredictor_combo X o β γ hab]
  simpa [smul_eq_mul] using (hc i).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

private lemma maximizer_unique_sum_terms (hinj : Function.Injective X.mulVec)
    (hs : ∀ i, StrictConcaveOn ℝ Set.univ (f i)) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (fun β => ∑ i, f i (linearPredictor X o β i)) Set.univ β₁)
    (h₂ : IsMaxOn (fun β => ∑ i, f i (linearPredictor X o β i)) Set.univ β₂) : β₁ = β₂ := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, linearPredictor X o β₁ j ≠ linearPredictor X o β₂ j := by
    by_contra hall
    push Not at hall
    exact hne (hinj (funext fun i => by simpa [linearPredictor_apply] using hall i))
  have hab : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hlt : (1 / 2 : ℝ) * ∑ i, f i (linearPredictor X o β₁ i) +
      1 / 2 * ∑ i, f i (linearPredictor X o β₂ i) <
      ∑ i, f i (linearPredictor X o ((1 / 2 : ℝ) • β₁ + (1 / 2 : ℝ) • β₂) i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, linearPredictor_combo X o β₁ β₂ hab]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · simpa [smul_eq_mul] using
        (hs i).concaveOn.2 (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num) hab
    · simpa [smul_eq_mul] using
        (hs j).2 (Set.mem_univ _) (Set.mem_univ _) hj (by norm_num) (by norm_num) hab
  have e₁ := h₁ (Set.mem_univ β₂)
  have e₂ := h₂ (Set.mem_univ β₁)
  have em := h₁ (Set.mem_univ ((1 / 2 : ℝ) • β₁ + (1 / 2 : ℝ) • β₂))
  simp only [Set.mem_ofPred_eq] at e₁ e₂ em
  linarith

private lemma strictConcaveOn_of_deriv (g g' g'' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hneg : ∀ x, g'' x < 0) :
    StrictConcaveOn ℝ Set.univ g := by
  have hd : deriv g = g' := funext fun x => (hg x).deriv
  refine strictConcaveOn_univ_of_deriv2_neg
    (continuous_iff_continuousAt.2 fun x => (hg x).continuousAt) fun x => ?_
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd, (hg' x).deriv]
  exact hneg x

end Engine

/-! ### The Bernoulli model with logit link -/

/-- The per-observation Bernoulli log likelihood in canonical form, for every real `y`:
`y log σ(η) + (1 - y) log (1 - σ(η)) = y η - log (1 + exp η)`. -/
theorem sigmoid_logLik_term (y η : ℝ) :
    y * log (sigmoid η) + (1 - y) * log (1 - sigmoid η) = y * η - log (1 + exp η) := by
  have h1 : 0 < 1 + exp η := by positivity
  have hs : sigmoid η = exp η / (1 + exp η) := by
    rw [sigmoid_def, exp_neg]
    field_simp
    ring
  have hs' : 1 - sigmoid η = 1 / (1 + exp η) := by
    rw [hs]
    field_simp
    ring
  rw [hs', hs, log_div (exp_pos η).ne' h1.ne', log_exp, one_div, log_inv]
  ring

private lemma hasDerivAt_log_one_add_exp (x : ℝ) :
    HasDerivAt (fun x => log (1 + exp x)) (sigmoid x) x := by
  have h := ((hasDerivAt_exp x).const_add 1).log (by positivity)
  convert h using 1
  rw [sigmoid_def, exp_neg]
  field_simp
  ring

private lemma hasDerivAt_logisticTerm (y x : ℝ) :
    HasDerivAt (fun x => y * x - log (1 + exp x)) (y - sigmoid x) x := by
  simpa using ((hasDerivAt_id x).const_mul y).fun_sub (hasDerivAt_log_one_add_exp x)

private lemma hasDerivAt_logisticScoreTerm (y x : ℝ) :
    HasDerivAt (fun x => y - sigmoid x) (-(sigmoid x * (1 - sigmoid x))) x := by
  simpa using (hasDerivAt_sigmoid x).const_sub y

private lemma strictConcaveOn_logisticTerm (y : ℝ) :
    StrictConcaveOn ℝ Set.univ (fun x => y * x - log (1 + exp x)) :=
  strictConcaveOn_of_deriv _ _ _ (hasDerivAt_logisticTerm y) (hasDerivAt_logisticScoreTerm y)
    fun x => neg_neg_of_pos (mul_pos (sigmoid_pos x) (sub_pos.2 (sigmoid_lt_one x)))

/-- The log likelihood of the canonical Bernoulli (logistic regression) model,
`ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - log (1 + exp ηᵢ(β)))`. For `yᵢ ∈ {0, 1}` each term is
`log P(Yᵢ = yᵢ)` under success probability `σ(ηᵢ)` (`sigmoid_logLik_term`). -/
noncomputable def logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  ∑ i, (y i * linearPredictor X o β i - log (1 + exp (linearPredictor X o β i)))

/-- **The logistic score.** The Fréchet derivative of the logistic log likelihood at `β` is
`v ↦ ⟪v, Xᵀ (y - σ(η(β)))⟫`. -/
theorem hasFDerivAt_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (logisticLogLik X o y)
      (Real.dotL (X.transpose *ᵥ (y - sigmoid ∘ linearPredictor X o β))) β :=
  hasFDerivAt_sum_terms X o (fun i x => y i * x - log (1 + exp x)) (fun i x => y i - sigmoid x)
    (fun i => hasDerivAt_logisticTerm (y i)) β

/-- The logistic score `Xᵀ (y - σ(η(β)))` is the gradient of the log likelihood on
`EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => logisticLogLik X o y b.ofLp)
      (WithLp.toLp 2 (X.transpose *ᵥ (y - sigmoid ∘ linearPredictor X o β))) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_logisticLogLik X o y β)

/-- **The logistic Hessian quadratic form.** Along `t ↦ β + t u` the second derivative at `0` is
`-∑ᵢ σ(ηᵢ)(1 - σ(ηᵢ)) ((X u)ᵢ)²`. -/
theorem deriv2_logisticLogLik_line (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => logisticLogLik X o y (β + t • u)) 0 =
      -∑ i, sigmoid (linearPredictor X o β i) * (1 - sigmoid (linearPredictor X o β i)) *
        (X *ᵥ u) i ^ 2 := by
  refine (deriv2_sum_terms_line X o (fun i x => y i * x - log (1 + exp x))
    (fun i x => y i - sigmoid x) (fun i x => -(sigmoid x * (1 - sigmoid x)))
    (fun i => hasDerivAt_logisticTerm (y i)) (fun i => hasDerivAt_logisticScoreTerm (y i))
    β u).trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The logistic log likelihood is concave on `κ → ℝ`. -/
theorem concaveOn_logisticLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) :
    ConcaveOn ℝ Set.univ (logisticLogLik X o y) :=
  concaveOn_sum_terms X o (fun i x => y i * x - log (1 + exp x))
    fun i => (strictConcaveOn_logisticTerm (y i)).concaveOn

/-- **At most one logistic maximum likelihood estimate.** If `β ↦ X β` is injective (full column
rank), the logistic log likelihood has at most one maximizer. The weights `σ(1 - σ)` are always
positive, so every term is strictly concave in its linear predictor. -/
theorem logisticLogLik_maximizer_unique (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (hX : Function.Injective X.mulVec) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (logisticLogLik X o y) Set.univ β₁)
    (h₂ : IsMaxOn (logisticLogLik X o y) Set.univ β₂) : β₁ = β₂ :=
  maximizer_unique_sum_terms X o (fun i x => y i * x - log (1 + exp x)) hX
    (fun i => strictConcaveOn_logisticTerm (y i)) h₁ h₂

private lemma log_one_add_exp (x : ℝ) : log (1 + exp x) = x + log (1 + exp (-x)) := by
  have e : 1 + exp x = exp x * (1 + exp (-x)) := by
    rw [mul_add, mul_one, ← exp_add, add_neg_cancel, exp_zero, add_comm]
  rw [e, log_mul (exp_pos x).ne' (by positivity), log_exp]

/-- Each binary logistic term is negative: `y η < log (1 + exp η)` for `y ∈ {0, 1}`. -/
theorem logisticTerm_neg {y : ℝ} (hy : y = 0 ∨ y = 1) (η : ℝ) :
    y * η - log (1 + exp η) < 0 := by
  have hpos : ∀ x : ℝ, 0 < log (1 + exp x) := fun x =>
    log_pos (by linarith [exp_pos x])
  rcases hy with rfl | rfl
  · linarith [hpos η]
  · rw [log_one_add_exp]
    linarith [hpos (-η)]

/-- For binary responses the logistic log likelihood is nonpositive. -/
theorem logisticLogLik_nonpos (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : logisticLogLik X o y β ≤ 0 :=
  Finset.sum_nonpos fun i _ => (logisticTerm_neg (hy i) _).le

/-! ### Complete separation: no logistic maximizer -/

/-- The single-covariate design `x = (-1, 1)` without intercept. -/
def separationDesign : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of ![![-1], ![1]]

/-- The separation design has full column rank: `β ↦ X β` is injective. -/
theorem separationDesign_mulVec_injective : Function.Injective separationDesign.mulVec := by
  intro β γ h
  have h1 := congrFun h 1
  simp only [separationDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.of_apply,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul] at h1
  funext k
  rw [Subsingleton.elim k 0]
  exact h1

/-- Under complete separation (`x = (-1, 1)`, `y = (0, 1)`, no offset) the logistic log likelihood
is `-2 log (1 + exp (-β))`. -/
theorem logisticLogLik_separation (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β = -2 * log (1 + exp (-β 0)) := by
  simp only [logisticLogLik, linearPredictor_apply, separationDesign, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply, add_zero, zero_mul, one_mul,
    neg_mul, zero_sub]
  rw [log_one_add_exp (β 0)]
  ring

/-- Under complete separation the logistic log likelihood is negative everywhere. -/
theorem logisticLogLik_separation_neg (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β < 0 := by
  rw [logisticLogLik_separation]
  have : 0 < log (1 + exp (-β 0)) := log_pos (by linarith [exp_pos (-β 0)])
  linarith

/-- Under complete separation every coefficient is beaten by a larger one. -/
theorem logisticLogLik_separation_lt (β : Fin 1 → ℝ) :
    logisticLogLik separationDesign 0 ![0, 1] β <
      logisticLogLik separationDesign 0 ![0, 1] (β + 1) := by
  rw [logisticLogLik_separation, logisticLogLik_separation]
  have : exp (-(β + 1) 0) < exp (-β 0) := exp_lt_exp.2 (by simp)
  have := log_lt_log (by positivity) (by linarith : 1 + exp (-(β + 1) 0) < 1 + exp (-β 0))
  linarith

/-- **Separation: no logistic maximum likelihood estimate**, although the design has full column
rank (`separationDesign_mulVec_injective`), so a maximizer would be unique. -/
theorem logisticLogLik_separation_not_isMaxOn (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (logisticLogLik separationDesign 0 ![0, 1]) Set.univ β := fun h =>
  (logisticLogLik_separation_lt β).not_ge (h (Set.mem_univ (β + 1)))

/-! ### Deviance -/

/-- The saturated Bernoulli log likelihood `∑ᵢ (yᵢ log yᵢ + (1 - yᵢ) log (1 - yᵢ)) = -∑ᵢ H(yᵢ)`
with `H = Real.binEntropy`; it is `0` for binary responses. -/
noncomputable def logisticLogLikSaturated (y : ι → ℝ) : ℝ :=
  -∑ i, binEntropy (y i)

theorem logisticLogLikSaturated_eq (y : ι → ℝ) :
    logisticLogLikSaturated y = ∑ i, (y i * log (y i) + (1 - y i) * log (1 - y i)) := by
  simp only [logisticLogLikSaturated, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    negMulLog, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem logisticLogLikSaturated_eq_zero (y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    logisticLogLikSaturated y = 0 := by
  simp only [logisticLogLikSaturated, neg_eq_zero]
  exact Finset.sum_eq_zero fun i _ => by rcases hy i with h | h <;> simp [h]

/-- The logistic deviance `2 (ℓ_sat - ℓ(β))`. -/
noncomputable def logisticDeviance (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  2 * (logisticLogLikSaturated y - logisticLogLik X o y β)

/-- For binary responses the deviance is `-2 ℓ(β)`. -/
theorem logisticDeviance_eq (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : logisticDeviance X o y β = -2 * logisticLogLik X o y β := by
  rw [logisticDeviance, logisticLogLikSaturated_eq_zero y hy]
  ring

/-- For binary responses the deviance is nonnegative. -/
theorem logisticDeviance_nonneg (X : Matrix ι κ ℝ) (o y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (β : κ → ℝ) : 0 ≤ logisticDeviance X o y β := by
  rw [logisticDeviance_eq X o y hy]
  linarith [logisticLogLik_nonpos X o y hy β]

/-! ### The Poisson model with log link -/

private lemma hasDerivAt_poissonTerm (y x : ℝ) :
    HasDerivAt (fun x => y * x - exp x) (y - exp x) x := by
  simpa using ((hasDerivAt_id x).const_mul y).fun_sub (hasDerivAt_exp x)

private lemma hasDerivAt_poissonScoreTerm (y x : ℝ) :
    HasDerivAt (fun x => y - exp x) (-exp x) x := by
  simpa using (hasDerivAt_exp x).const_sub y

private lemma strictConcaveOn_poissonTerm (y : ℝ) :
    StrictConcaveOn ℝ Set.univ (fun x => y * x - exp x) :=
  strictConcaveOn_of_deriv _ _ _ (hasDerivAt_poissonTerm y) (hasDerivAt_poissonScoreTerm y)
    fun x => neg_neg_of_pos (exp_pos x)

/-- The log likelihood of the canonical Poisson (log-linear) model up to an additive constant,
`ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - exp ηᵢ(β))`. The omitted term `-∑ᵢ log yᵢ!` does not depend on `β`. -/
noncomputable def poissonLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) : ℝ :=
  ∑ i, (y i * linearPredictor X o β i - exp (linearPredictor X o β i))

/-- **The Poisson score.** The Fréchet derivative of the Poisson log likelihood at `β` is
`v ↦ ⟪v, Xᵀ (y - exp (η(β)))⟫`. -/
theorem hasFDerivAt_poissonLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasFDerivAt (poissonLogLik X o y)
      (Real.dotL (X.transpose *ᵥ (y - exp ∘ linearPredictor X o β))) β :=
  hasFDerivAt_sum_terms X o (fun i x => y i * x - exp x) (fun i x => y i - exp x)
    (fun i => hasDerivAt_poissonTerm (y i)) β

/-- The Poisson score `Xᵀ (y - exp (η(β)))` is the gradient of the log likelihood on
`EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_poissonLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β : κ → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => poissonLogLik X o y b.ofLp)
      (WithLp.toLp 2 (X.transpose *ᵥ (y - exp ∘ linearPredictor X o β))) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_poissonLogLik X o y β)

/-- **The Poisson Hessian quadratic form.** Along `t ↦ β + t u` the second derivative at `0` is
`-∑ᵢ exp ηᵢ ((X u)ᵢ)²`. -/
theorem deriv2_poissonLogLik_line (X : Matrix ι κ ℝ) (o y : ι → ℝ) (β u : κ → ℝ) :
    deriv^[2] (fun t : ℝ => poissonLogLik X o y (β + t • u)) 0 =
      -∑ i, exp (linearPredictor X o β i) * (X *ᵥ u) i ^ 2 := by
  refine (deriv2_sum_terms_line X o (fun i x => y i * x - exp x) (fun i x => y i - exp x)
    (fun i x => -exp x) (fun i => hasDerivAt_poissonTerm (y i))
    (fun i => hasDerivAt_poissonScoreTerm (y i)) β u).trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The Poisson log likelihood is concave on `κ → ℝ`. -/
theorem concaveOn_poissonLogLik (X : Matrix ι κ ℝ) (o y : ι → ℝ) :
    ConcaveOn ℝ Set.univ (poissonLogLik X o y) :=
  concaveOn_sum_terms X o (fun i x => y i * x - exp x)
    fun i => (strictConcaveOn_poissonTerm (y i)).concaveOn

/-- **At most one Poisson maximum likelihood estimate** when `β ↦ X β` is injective. -/
theorem poissonLogLik_maximizer_unique (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (hX : Function.Injective X.mulVec) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (poissonLogLik X o y) Set.univ β₁)
    (h₂ : IsMaxOn (poissonLogLik X o y) Set.univ β₂) : β₁ = β₂ :=
  maximizer_unique_sum_terms X o (fun i x => y i * x - exp x) hX
    (fun i => strictConcaveOn_poissonTerm (y i)) h₁ h₂

/-! ### All-zero counts: no Poisson maximizer -/

/-- With all-zero counts, an intercept-only design and no offset, the Poisson log likelihood is
`-|ι| exp β`. -/
theorem poissonLogLik_allZero (β : Fin 1 → ℝ) :
    poissonLogLik (Matrix.of fun (_ : ι) (_ : Fin 1) => (1 : ℝ)) 0 0 β =
      -(Fintype.card ι * exp (β 0)) := by
  simp [poissonLogLik, linearPredictor_apply, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

/-- **All-zero counts: no Poisson maximum likelihood estimate** (at least one observation):
lowering the intercept always increases the likelihood. -/
theorem poissonLogLik_allZero_not_isMaxOn [Nonempty ι] (β : Fin 1 → ℝ) :
    ¬ IsMaxOn (poissonLogLik (Matrix.of fun (_ : ι) (_ : Fin 1) => (1 : ℝ)) 0 0) Set.univ β := by
  intro h
  have hle := h (Set.mem_univ (β - 1))
  simp only [Set.mem_ofPred_eq, poissonLogLik_allZero, Pi.sub_apply, Pi.one_apply] at hle
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have : exp (β 0 - 1) < exp (β 0) := exp_lt_exp.2 (by linarith)
  nlinarith

end MathlibExt.Probability.Statistics.GLM
