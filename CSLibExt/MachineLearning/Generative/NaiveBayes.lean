/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.Categorical
public import MathlibExt.Algebra.BigOperators.ProdCompPow
public import MathlibExt.Analysis.SpecialFunctions.SigmoidLogOdds
public import Mathlib.Data.Fintype.Pi

/-!
# Naive Bayes classifiers

A naive Bayes model has a prior `π` on a finite set of classes `C` and, for each class `c` and
each feature `i`, a distribution `θ c i` on the feature's finitely many values `V i`; all are
points of Mathlib's standard simplex `Convexity.StdSimplex`. Features are independent given the
class, so the joint probability of a class and a feature vector is
`joint c x = π c * ∏ i, θ c i (x i)`. With binary features (`V i = Bool`) this is the Bernoulli
model; the multinomial (bag-of-words) model is the second half of the file.

## Main definitions and results

Categorical-feature (including Bernoulli) model, `Params C ι V`:
* `Params.joint`, `Params.posterior`; `sum_joint`: the joint is a probability distribution;
  `sum_posterior`: the posterior is a distribution when the evidence is positive; `log_joint`:
  for positive weights, the log joint is the log prior plus a sum of per-feature log
  probabilities.
* `classify`: the classifier picks a class of maximal joint probability, and when the evidence is
  positive also of maximal posterior probability (`posterior_le_classify`).
  `accuracy_le_classify`: no classifier is correct with higher probability under the model (the
  Bayes classifier); `risk_classify_le`:
  equivalently it minimizes the expected 0-1 loss. The general measure-theoretic statement, for
  any prior and class-conditional laws, is `BayesClassifier.IsPosteriorArgmax.isBayesEstimator`
  (`BayesClassifier.lean`), built on Mathlib's
  `ProbabilityTheory.IsArgminEstimator.isBayesEstimator`.
* `likelihood_eq`: the likelihood of labelled data factors into a categorical likelihood for the
  prior and one for each class and feature; `likelihood_le_mle`: hence `mle`, built from the
  categorical estimates of each factor (`Categorical.likelihood_le_mle`), maximizes the
  likelihood. When the denominators are positive its weights are the normalized counts
  `π̂ c = N_c / m` and `θ̂ c i v = N_{c,i,v} / N_c` (`mle_prior_apply`, `mle_cond_apply`); with no
  data or for a class without examples the corresponding factor of the likelihood is constant and
  `mle` chooses the uniform distribution. For each categorical factor separately, add-one
  smoothing of its counts is a MAP estimate under the Dirichlet prior with concentrations `2`
  (`Categorical.isMaxOn_posterior_laplace`).
* `posterior_true_eq_sigmoid`: with two classes, binary features and strictly positive prior and
  conditional probabilities, the posterior is the logistic function of an affine function of the
  features (`bernoulliWeight`, `bernoulliBias`), the link between naive Bayes and logistic
  regression. Positivity is needed: `StdSimplex` allows zero weights (and `mle` produces them
  for unseen values), and then the posterior can be exactly `0` or `1`, which no finite logistic
  score gives.

Multinomial model, `MultParams C W` (word distributions per class, documents as word counts):
* `MultParams.log_joint`: for positive weights, the log joint is linear in the word counts.
* `MultParams.likelihood_le_mle`: `mle` maximizes the likelihood; when a class has at least one
  word its word distribution is the normalized total word counts of the class (uniform
  otherwise). `MultParams.isMaxOn_word_laplace`: for each class, add-one smoothing of its word
  counts is a MAP estimate under the Dirichlet prior with concentrations `2`.

The multinomial `joint` is a mass kernel: it omits the multinomial coefficient of the document,
which depends on neither the class nor the parameters, so it is not normalized over count
vectors.

Two generic helpers come from MathlibExt: `Fintype.prod_comp_eq_prod_pow` (a product over examples
regrouped by value) and `Real.sigmoid_log_sub_log` (`a / (a + b)` is the logistic function of
`log a - log b`).
-/

@[expose] public section

namespace Cslib.MachineLearning

open Finset Categorical Convexity

namespace NaiveBayes

section Counts

variable {C : Type*} [Fintype C] [DecidableEq C] {m : ℕ} (y : Fin m → C)

/-- The number of examples of class `c`. -/
def classCount (c : C) : ℕ :=
  (univ.filter fun k => y k = c).card

theorem sum_classCount : ∑ c, classCount y c = m := by
  simp only [classCount]
  rw [← card_eq_sum_card_fiberwise fun k _ => mem_univ (y k), card_univ, Fintype.card_fin]

end Counts

/-- Parameters of a naive Bayes model with categorical features: a prior on the classes and, for
each class and feature, a distribution on the feature's values. -/
structure Params (C ι : Type*) (V : ι → Type*) where
  /-- The class prior. -/
  prior : StdSimplex ℝ C
  /-- The distribution of feature `i` given class `c`. -/
  cond : C → (i : ι) → StdSimplex ℝ (V i)

namespace Params

variable {C ι : Type*} {V : ι → Type*} [Fintype C] [Fintype ι] [∀ i, Fintype (V i)]

/-- The joint probability of class `c` and features `x`: the features are independent given the
class. -/
noncomputable def joint (p : Params C ι V) (c : C) (x : ∀ i, V i) : ℝ :=
  p.prior.weights c * ∏ i, (p.cond c i).weights (x i)

/-- The probability of the features. -/
noncomputable def evidence (p : Params C ι V) (x : ∀ i, V i) : ℝ :=
  ∑ c, p.joint c x

/-- The posterior probability of class `c` given the features: `joint c x / evidence x`. It is a
probability distribution on the classes when the evidence is positive (`sum_posterior`); when
every class gives the features probability zero, the evidence is `0` and Lean's division makes
every score `0`. -/
noncomputable def posterior (p : Params C ι V) (x : ∀ i, V i) (c : C) : ℝ :=
  p.joint c x / p.evidence x

variable {p : Params C ι V}

omit [Fintype C] [∀ i, Fintype (V i)] in
theorem joint_nonneg (p : Params C ι V) (c : C) (x : ∀ i, V i) : 0 ≤ p.joint c x :=
  mul_nonneg (p.prior.nonneg c) (prod_nonneg fun i _ => (p.cond c i).nonneg _)

omit [∀ i, Fintype (V i)] in
theorem evidence_nonneg (p : Params C ι V) (x : ∀ i, V i) : 0 ≤ p.evidence x :=
  sum_nonneg fun c _ => joint_nonneg p c x

/-- The joint is a probability distribution on classes and feature vectors. -/
theorem sum_joint [DecidableEq ι] (p : Params C ι V) : ∑ c, ∑ x, p.joint c x = 1 := by
  have h : ∀ c, ∑ x : ∀ i, V i, ∏ i, (p.cond c i).weights (x i) = 1 := fun c => by
    rw [← Fintype.prod_sum]
    exact prod_eq_one fun i _ => (p.cond c i).total_of_fintype
  simp only [joint, ← mul_sum, h, mul_one]
  exact p.prior.total_of_fintype

omit [∀ i, Fintype (V i)] in
theorem posterior_nonneg (p : Params C ι V) (x : ∀ i, V i) (c : C) : 0 ≤ p.posterior x c :=
  div_nonneg (joint_nonneg p c x) (evidence_nonneg p x)

omit [∀ i, Fintype (V i)] in
/-- The posterior is a probability distribution on the classes. -/
theorem sum_posterior {x : ∀ i, V i} (hx : 0 < p.evidence x) : ∑ c, p.posterior x c = 1 := by
  simp only [posterior, ← sum_div]
  exact div_self hx.ne'

omit [∀ i, Fintype (V i)] in
theorem posterior_le_posterior_iff {x : ∀ i, V i} (hx : 0 < p.evidence x) {c c' : C} :
    p.posterior x c ≤ p.posterior x c' ↔ p.joint c x ≤ p.joint c' x :=
  div_le_div_iff_of_pos_right hx

omit [Fintype C] [∀ i, Fintype (V i)] in
/-- For positive weights, the log joint is the log prior plus the per-feature log
probabilities. -/
theorem log_joint {c : C} {x : ∀ i, V i} (hprior : 0 < p.prior.weights c)
    (hcond : ∀ i, 0 < (p.cond c i).weights (x i)) :
    Real.log (p.joint c x) =
      Real.log (p.prior.weights c) + ∑ i, Real.log ((p.cond c i).weights (x i)) := by
  rw [joint, Real.log_mul hprior.ne' (prod_pos fun i _ => hcond i).ne',
    Real.log_prod fun i _ => (hcond i).ne']

/-! ### The classifier -/

/-- The naive Bayes classifier: a class of maximal joint probability. -/
noncomputable def classify [Nonempty C] (p : Params C ι V) (x : ∀ i, V i) : C :=
  (exists_max_image univ (p.joint · x) univ_nonempty).choose

omit [∀ i, Fintype (V i)] in
theorem joint_le_classify [Nonempty C] (p : Params C ι V) (x : ∀ i, V i) (c : C) :
    p.joint c x ≤ p.joint (p.classify x) x :=
  (exists_max_image univ (p.joint · x) univ_nonempty).choose_spec.2 c (mem_univ c)

omit [∀ i, Fintype (V i)] in
/-- When the evidence is positive, the classifier picks a class of maximal posterior
probability. -/
theorem posterior_le_classify [Nonempty C] {x : ∀ i, V i} (hx : 0 < p.evidence x) (c : C) :
    p.posterior x c ≤ p.posterior x (p.classify x) :=
  (posterior_le_posterior_iff hx).2 (joint_le_classify p x c)

/-- The probability under the model that the classifier `h` predicts the class. -/
noncomputable def accuracy [DecidableEq ι] (p : Params C ι V) (h : (∀ i, V i) → C) : ℝ :=
  ∑ x, p.joint (h x) x

/-- The expected 0-1 loss of the classifier `h` under the model. -/
noncomputable def risk [DecidableEq ι] [DecidableEq C] (p : Params C ι V)
    (h : (∀ i, V i) → C) : ℝ :=
  ∑ c, ∑ x, if h x = c then 0 else p.joint c x

/-- **Bayes optimality**: no classifier is correct with higher probability under the model. -/
theorem accuracy_le_classify [DecidableEq ι] [Nonempty C] (p : Params C ι V)
    (h : (∀ i, V i) → C) : p.accuracy h ≤ p.accuracy p.classify :=
  sum_le_sum fun x _ => joint_le_classify p x (h x)

theorem risk_eq [DecidableEq ι] [DecidableEq C] (p : Params C ι V) (h : (∀ i, V i) → C) :
    p.risk h = 1 - p.accuracy h := by
  have hx : ∀ x, ∑ c, (if h x = c then 0 else p.joint c x) = p.evidence x - p.joint (h x) x :=
    fun x => by
      rw [evidence, ← sum_erase_add _ _ (mem_univ (h x)), ite_eq_left rfl, add_zero,
        ← sum_erase_add _ _ (mem_univ (h x)), add_sub_cancel_right]
      exact sum_congr rfl fun c hc => ite_eq_right (ne_of_mem_erase hc).symm
  rw [risk, sum_comm, sum_congr rfl fun x _ => hx x, sum_sub_distrib, accuracy, ← sum_joint p,
    sum_comm]
  rfl

/-- **Bayes optimality**: the classifier minimizes the expected 0-1 loss under the model. -/
theorem risk_classify_le [DecidableEq ι] [DecidableEq C] [Nonempty C] (p : Params C ι V)
    (h : (∀ i, V i) → C) : p.risk p.classify ≤ p.risk h := by
  rw [risk_eq p, risk_eq p]
  linarith [accuracy_le_classify p h]

/-! ### Maximum likelihood estimation -/

section MLE

variable [DecidableEq C] [∀ i, DecidableEq (V i)] {m : ℕ} (y : Fin m → C)
  (x : Fin m → ∀ i, V i)

/-- The likelihood of labelled data `(y k, x k)`. -/
noncomputable def likelihood (p : Params C ι V) : ℝ :=
  ∏ k, p.joint (y k) (x k)

/-- The number of examples of class `c` whose feature `i` has value `v`. -/
def featCount (c : C) (i : ι) (v : V i) : ℕ :=
  (univ.filter fun k => y k = c ∧ x k i = v).card

omit [Fintype C] [Fintype ι] in
theorem sum_featCount (c : C) (i : ι) : ∑ v, featCount y x c i v = classCount y c := by
  rw [classCount, card_eq_sum_card_fiberwise (f := fun k => x k i) fun k _ => mem_univ _]
  refine sum_congr rfl fun v _ => ?_
  rw [featCount, filter_filter]

omit [Fintype C] [Fintype ι] [∀ i, Fintype (V i)] in
theorem featCount_le (c : C) (i : ι) (v : V i) : featCount y x c i v ≤ classCount y c :=
  card_le_card fun k hk => by
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.1

/-- The maximum likelihood estimate (`likelihood_le_mle`): normalized class counts and normalized
feature counts within each class, with the uniform distribution for a class without examples and
the uniform prior without data. -/
noncomputable def mle [Nonempty C] [∀ i, Nonempty (V i)] : Params C ι V where
  prior := Categorical.mle (classCount y)
  cond c i := Categorical.mle (featCount y x c i)

omit [Fintype ι] in
theorem mle_prior_apply [Nonempty C] [∀ i, Nonempty (V i)] (hm : 0 < m) (c : C) :
    (mle (V := V) y x).prior.weights c = classCount y c / m := by
  simp only [mle]
  rw [Categorical.mle_apply (by rw [sum_classCount]; exact hm), sum_classCount]

omit [Fintype ι] in
theorem mle_cond_apply [Nonempty C] [∀ i, Nonempty (V i)] {c : C} (hc : classCount y c ≠ 0)
    (i : ι) (v : V i) :
    ((mle y x).cond c i).weights v = featCount y x c i v / classCount y c := by
  simp only [mle]
  rw [Categorical.mle_apply (by rw [sum_featCount]; exact Nat.pos_of_ne_zero hc),
    sum_featCount]

/-- The likelihood factors into a categorical likelihood for the prior and one for each class and
feature. -/
theorem likelihood_eq (p : Params C ι V) :
    likelihood y x p = Categorical.likelihood p.prior (classCount y) *
      ∏ i, ∏ c, Categorical.likelihood (p.cond c i) (featCount y x c i) := by
  rw [likelihood]
  simp only [joint, Categorical.likelihood]
  rw [prod_mul_distrib, Fintype.prod_comp_eq_prod_pow y p.prior.weights, prod_comm]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_comp_eq_prod_pow (fun k => (y k, x k i))
      fun cv => (p.cond cv.1 i).weights cv.2,
    Fintype.prod_prod_type]
  refine prod_congr rfl fun c _ => prod_congr rfl fun v _ => ?_
  simp only [featCount, Prod.mk.injEq]

/-- **Maximum likelihood estimation**: the normalized counts maximize the likelihood over all
parameters. -/
theorem likelihood_le_mle [Nonempty C] [∀ i, Nonempty (V i)] (p : Params C ι V) :
    likelihood y x p ≤ likelihood y x (mle y x) := by
  rw [likelihood_eq, likelihood_eq]
  refine mul_le_mul (Categorical.likelihood_le_mle _ _) ?_
    (prod_nonneg fun i _ => prod_nonneg fun c _ => likelihood_nonneg _ _) (likelihood_nonneg _ _)
  exact prod_le_prod₀ (fun i _ => prod_nonneg fun c _ => likelihood_nonneg _ _) fun i _ =>
    prod_le_prod₀ (fun c _ => likelihood_nonneg _ _) fun c _ => Categorical.likelihood_le_mle _ _

end MLE

/-! ### Two classes and binary features: the posterior is logistic -/

section Bernoulli

variable (q : Params Bool ι fun _ => Bool)

/-- The weight of feature `i` in the log posterior odds, when all prior and conditional
probabilities are strictly positive (`log_joint_sub`). -/
noncomputable def bernoulliWeight (i : ι) : ℝ :=
  Real.log ((q.cond true i).weights true * (q.cond false i).weights false /
    ((q.cond false i).weights true * (q.cond true i).weights false))

/-- The bias of the log posterior odds, when all prior and conditional probabilities are strictly
positive (`log_joint_sub`). -/
noncomputable def bernoulliBias : ℝ :=
  Real.log (q.prior.weights true / q.prior.weights false) +
    ∑ i, Real.log ((q.cond true i).weights false / (q.cond false i).weights false)

variable {q}

/-- With two classes, binary features and positive probabilities, the log ratio of the joint
probabilities, which equals the log posterior odds, is affine in the features. -/
theorem log_joint_sub (hprior : ∀ c, 0 < q.prior.weights c)
    (hcond : ∀ c i v, 0 < (q.cond c i).weights v) (x : ι → Bool) :
    Real.log (q.joint true x) - Real.log (q.joint false x) =
      bernoulliBias q + ∑ i, bernoulliWeight q i * if x i then 1 else 0 := by
  rw [log_joint (hprior _) fun i => hcond _ _ _, log_joint (hprior _) fun i => hcond _ _ _]
  have hi : ∀ i, Real.log ((q.cond true i).weights (x i)) -
      Real.log ((q.cond false i).weights (x i)) =
      Real.log ((q.cond true i).weights false / (q.cond false i).weights false) +
        bernoulliWeight q i * if x i then 1 else 0 := fun i => by
    have h1 := hcond true i true
    have h2 := hcond false i true
    have h3 := hcond true i false
    have h4 := hcond false i false
    rcases x i with _ | _
    · simp [Real.log_div h3.ne' h4.ne']
    · simp only [bernoulliWeight, ↓reduceIte, mul_one]
      rw [Real.log_div h3.ne' h4.ne', Real.log_div (mul_pos h1 h4).ne' (mul_pos h2 h3).ne',
        Real.log_mul h1.ne' h4.ne', Real.log_mul h2.ne' h3.ne']
      ring
  rw [bernoulliBias, Real.log_div (hprior _).ne' (hprior _).ne']
  have := sum_congr rfl fun i (_ : i ∈ univ) => hi i
  rw [sum_sub_distrib, sum_add_distrib] at this
  linarith

/-- **Naive Bayes is logistic in its posterior**: with two classes, binary features and strictly
positive prior and conditional probabilities, the posterior probability of the class `true` is
the logistic function of an affine function of the features. Without positivity the posterior
can be exactly `0` or `1`, which no finite logistic score gives. -/
theorem posterior_true_eq_sigmoid (hprior : ∀ c, 0 < q.prior.weights c)
    (hcond : ∀ c i v, 0 < (q.cond c i).weights v) (x : ι → Bool) :
    q.posterior x true =
      Real.sigmoid (bernoulliBias q + ∑ i, bernoulliWeight q i * if x i then 1 else 0) := by
  have hpos : ∀ c, 0 < q.joint c x := fun c =>
    mul_pos (hprior c) (prod_pos fun i _ => hcond c i (x i))
  rw [← log_joint_sub hprior hcond, Real.sigmoid_log_sub_log (hpos true) (hpos false), posterior,
    evidence, Fintype.sum_bool]

end Bernoulli

end Params

/-! ## The multinomial model -/

/-- Parameters of a multinomial naive Bayes model: a prior on the classes and, for each class, a
distribution on the words. -/
structure MultParams (C W : Type*) where
  /-- The class prior. -/
  prior : StdSimplex ℝ C
  /-- The word distribution of class `c`. -/
  word : C → StdSimplex ℝ W

namespace MultParams

variable {C W : Type*} [Fintype C] [Fintype W]

/-- The joint mass kernel of class `c` and a document with word counts `x`: the joint probability
up to the multinomial coefficient of the document, which depends on neither the class nor the
parameters. -/
noncomputable def joint (p : MultParams C W) (c : C) (x : W → ℕ) : ℝ :=
  p.prior.weights c * ∏ w, (p.word c).weights w ^ x w

variable {p : MultParams C W}

omit [Fintype C] in
/-- For positive weights, the log joint is linear in the word counts. -/
theorem log_joint {c : C} (hprior : 0 < p.prior.weights c) (hword : ∀ w, 0 < (p.word c).weights w)
    (x : W → ℕ) :
    Real.log (p.joint c x) =
      Real.log (p.prior.weights c) + ∑ w, (x w : ℝ) * Real.log ((p.word c).weights w) := by
  rw [joint, Real.log_mul hprior.ne' (prod_pos fun w _ => pow_pos (hword w) _).ne',
    Real.log_prod fun w _ => (pow_pos (hword w) _).ne']
  simp only [Real.log_pow]

variable [DecidableEq C] {m : ℕ} (y : Fin m → C) (x : Fin m → W → ℕ)

/-- The likelihood of labelled documents `(y k, x k)`. -/
noncomputable def likelihood (p : MultParams C W) : ℝ :=
  ∏ k, p.joint (y k) (x k)

/-- The total count of word `w` in the documents of class `c`. -/
def wordCount (c : C) (w : W) : ℕ :=
  ∑ k ∈ univ.filter fun k => y k = c, x k w

/-- The maximum likelihood estimate (`MultParams.likelihood_le_mle`): normalized class counts and
normalized total word counts within each class, uniform without data or for a class without
words. -/
noncomputable def mle [Nonempty C] [Nonempty W] : MultParams C W where
  prior := Categorical.mle (classCount y)
  word c := Categorical.mle (wordCount y x c)

theorem likelihood_eq (p : MultParams C W) :
    likelihood y x p = Categorical.likelihood p.prior (classCount y) *
      ∏ c, Categorical.likelihood (p.word c) (wordCount y x c) := by
  rw [likelihood]
  simp only [joint, Categorical.likelihood]
  rw [prod_mul_distrib, Fintype.prod_comp_eq_prod_pow y p.prior.weights]
  congr 1
  rw [← prod_fiberwise univ y fun k => ∏ w, (p.word (y k)).weights w ^ x k w]
  refine prod_congr rfl fun c _ => ?_
  rw [prod_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], prod_comm]
  exact prod_congr rfl fun w _ => prod_pow_eq_pow_sum _ _ _

/-- **Maximum likelihood estimation** for the multinomial model. -/
theorem likelihood_le_mle [Nonempty C] [Nonempty W] (p : MultParams C W) :
    likelihood y x p ≤ likelihood y x (mle y x) := by
  rw [likelihood_eq, likelihood_eq]
  refine mul_le_mul (Categorical.likelihood_le_mle _ _) ?_
    (prod_nonneg fun c _ => likelihood_nonneg _ _) (likelihood_nonneg _ _)
  exact prod_le_prod₀ (fun c _ => likelihood_nonneg _ _) fun c _ =>
    Categorical.likelihood_le_mle _ _

omit [Fintype C] in
/-- **Laplace smoothing** of the word counts of a class is the MAP estimate of its word
distribution under the Dirichlet prior with concentrations `2`. -/
theorem isMaxOn_word_laplace [Nonempty W] (c : C) :
    IsMaxOn (fun θ => Categorical.likelihood θ (wordCount y x c) *
      dirichletKernel (fun _ => 2) θ) Set.univ (laplace (wordCount y x c)) :=
  isMaxOn_posterior_laplace _

end MultParams

end Cslib.MachineLearning.NaiveBayes
