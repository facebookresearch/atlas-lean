/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Basic
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic

/-!
# The Bayes classifier

Classification with countably many classes `C`: an observation `x` is drawn from the
class-conditional law `P c` of its class `c` (a Markov kernel `P : Kernel C 𝓧`), and the class
from a prior `π`. A (possibly randomized) classifier is a Markov kernel `κ : Kernel 𝓧 C`, and a
deterministic one is a measurable map `f : 𝓧 → C`. Its quality is measured by the 0-1 loss
`zeroOneLoss c y` (`1` for a wrong prediction `y`, `0` for the true class `c`). In Mathlib's
decision-theory framework (`Mathlib/Probability/Decision/`), the expected 0-1 loss of `κ` is
`avgRisk zeroOneLoss P κ π`, and the Bayes risk `bayesRisk zeroOneLoss P π` is its infimum over
all classifiers.

* `avgRisk_zeroOneLoss_deterministic`: the 0-1 risk of `f` is `∫ π(dc) P c {x | f x ≠ c}`, the
  prior average of its misclassification probabilities (for Markov `P`).
* `lintegral_zeroOneLoss`, `lintegral_zeroOneLoss_eq_one_sub`: the posterior expected 0-1 loss
  of predicting `y` is the posterior mass of `{y}ᶜ`, that is `1 - P†π x {y}`.
* `IsPosteriorArgmax`: `f` is measurable and, for almost every observation, picks a class of
  maximal posterior probability.
* `IsPosteriorArgmax.isBayesEstimator`, `IsPosteriorArgmax.avgRisk_le` (**the Bayes classifier
  is optimal**): a posterior argmax classifier minimizes the expected 0-1 loss over all
  classifiers, randomized ones included. The proof identifies it as an argmin estimator of the
  posterior expected loss (`IsPosteriorArgmax.isArgminEstimator`) and applies Mathlib's
  `ProbabilityTheory.IsArgminEstimator.isBayesEstimator`.
* `exists_isPosteriorArgmax`: for finitely many classes a measurable posterior argmax exists, so
  `bayesRisk_zeroOneLoss`: the Bayes risk is `∫ (P ∘ₘ π)(dx) ⨅ y, P†π x {y}ᶜ`.
* `isPosteriorArgmax_of_isMAP`: for countable observations, classifying each observation of
  positive evidence by a maximum a posteriori class (`Bayesian.IsMAP`, equivalently by maximal
  prior times likelihood, `Bayesian.isMAP_iff`) is a posterior argmax classifier, hence Bayes
  optimal. Observations of zero evidence form a null set and may be classified arbitrarily.

* `isPosteriorArgmax_iff_isArgminEstimator`: conversely, every argmin estimator of the posterior
  expected 0-1 loss is a posterior argmax classifier.

The classifier is the Bayes classifier of a generative model (prior and class-conditional laws);
naive Bayes (`NaiveBayes.risk_classify_le`) and Gaussian discriminant analysis are instances
with finitely many classes. The finite, binary-label form of the optimality statement, with the
joint law given by weights, is Exercise 3.7 of Shalev-Shwartz and Ben-David, *Understanding
Machine Learning* (`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/`
`Exercises.lean`, `ex_3_7`).
-/

@[expose] public section

namespace Cslib.MachineLearning.BayesClassifier

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {C 𝓧 : Type*}

/-- **The 0-1 loss.** For elements $c$ and $y$ of a type $C$ of classes, the 0-1 loss of
predicting $y$ when the true class is $c$ is the extended nonnegative real number that equals
$0$ if $y = c$ and $1$ if $y \ne c$. -/
noncomputable def zeroOneLoss (c y : C) : ℝ≥0∞ :=
  ({y}ᶜ : Set C).indicator 1 c

theorem zeroOneLoss_apply [DecidableEq C] (c y : C) :
    zeroOneLoss c y = if c = y then 0 else 1 := by
  by_cases h : c = y <;> simp [zeroOneLoss, h]

theorem zeroOneLoss_comm (c y : C) : zeroOneLoss c y = zeroOneLoss y c := by
  classical
  simp only [zeroOneLoss_apply, eq_comm]

variable [MeasurableSpace C] [MeasurableSpace 𝓧]

theorem measurable_zeroOneLoss [Countable C] [MeasurableSingletonClass C] :
    Measurable (Function.uncurry (zeroOneLoss (C := C))) :=
  measurable_of_countable _

/-- **Expected 0-1 loss of a fixed prediction.** Let $C$ be a measurable space in which every
singleton is measurable, let $\nu$ be a measure on $C$, and let $y \in C$. Writing $\ell(c, y)$
for the 0-1 loss of predicting $y$ when the true class is $c$, we have
$\int \ell(c, y) \, d\nu(c) = \nu(C \setminus \{y\})$. -/
theorem lintegral_zeroOneLoss [MeasurableSingletonClass C] (ν : Measure C) (y : C) :
    ∫⁻ c, zeroOneLoss c y ∂ν = ν {y}ᶜ :=
  lintegral_indicator_one (measurableSet_singleton y).compl

/-- **Integrating the 0-1 loss over the prediction.** Let $C$ be a measurable space with
measurable singletons, $\nu$ a measure on $C$ and $c \in C$, and let $\ell(c, y)$ be the 0-1
loss of predicting $y$ when the true class is $c$ ($0$ if $y = c$, $1$ otherwise). Then
$\int_C \ell(c, y)\,\nu(dy) = \nu(C \setminus \{c\})$.

When $\nu$ is the law of a random prediction, this is its expected 0-1 loss when the true class
is $c$. -/
theorem lintegral_zeroOneLoss_right [MeasurableSingletonClass C] (ν : Measure C) (c : C) :
    ∫⁻ y, zeroOneLoss c y ∂ν = ν {c}ᶜ := by
  simp_rw [zeroOneLoss_comm c]
  exact lintegral_zeroOneLoss ν c

theorem lintegral_zeroOneLoss_eq_one_sub [MeasurableSingletonClass C] (ν : Measure C)
    [IsProbabilityMeasure ν] (y : C) : ∫⁻ c, zeroOneLoss c y ∂ν = 1 - ν {y} := by
  rw [lintegral_zeroOneLoss, prob_compl_eq_one_sub (measurableSet_singleton y)]

/-- **The 0-1 risk of a deterministic classifier.** Let $C$ be a measurable space of classes with
measurable singletons, $P$ a kernel from $C$ to the observation space $\mathcal X$, $\pi$ a
measure on $C$, $f : \mathcal X \to C$ a measurable map, and $\ell(c, y)$ the 0-1 loss ($0$ if
$y = c$, $1$ otherwise). Then the average 0-1 risk of the deterministic kernel
$\delta_f : x \mapsto \delta_{f(x)}$,
$\int_C \int_C \ell(c, y)\,(\delta_f \circ P)(c)(dy)\,\pi(dc)$ with
$(\delta_f \circ P)(c) = \int_{\mathcal X} \delta_{f(x)}\,P(c)(dx)$, equals
$\int_C P(c)(\{x \in \mathcal X : f(x) \ne c\})\,\pi(dc)$.

When each $P(c)$ is a probability measure, $P(c)(\{x : f(x) \ne c\})$ is the probability that
$f$ misclassifies an observation of class $c$. -/
theorem avgRisk_zeroOneLoss_deterministic [MeasurableSingletonClass C] (P : Kernel C 𝓧)
    (π : Measure C) {f : 𝓧 → C} (hf : Measurable f) :
    avgRisk zeroOneLoss P (Kernel.deterministic f hf) π = ∫⁻ c, P c {x | f x ≠ c} ∂π := by
  rw [avgRisk]
  refine lintegral_congr fun c => ?_
  rw [Kernel.deterministic_comp_eq_map, Kernel.map_apply _ hf, lintegral_zeroOneLoss_right,
    Measure.map_apply hf (measurableSet_singleton c).compl]
  rfl

section Countable

variable [Countable C] [MeasurableSingletonClass C] [Nonempty C]

/-- **Posterior argmax classifier.** Let the set $C$ of classes be countable and nonempty with
measurable singletons, let $P$ be a finite kernel from $C$ to the observation space $\mathcal X$
and $\pi$ a finite measure on $C$, write $P \circ \pi$ for the marginal measure on $\mathcal X$
and $P^\dagger_\pi$ for the posterior kernel from $\mathcal X$ to $C$. A map
$f : \mathcal X \to C$ is a posterior argmax classifier for $P$ and $\pi$ if $f$ is measurable
and, for $(P \circ \pi)$-almost every $x$,
$P^\dagger_\pi(x)(\{y\}) \le P^\dagger_\pi(x)(\{f(x)\})$ for every $y \in C$.

Countably many classes with measurable singletons make the posterior masses of classes
meaningful, and give the standard Borel structure the posterior needs. -/
structure IsPosteriorArgmax (P : Kernel C 𝓧) [IsFiniteKernel P] (π : Measure C)
    [IsFiniteMeasure π] (f : 𝓧 → C) : Prop where
  measurable : Measurable f
  ae_le : ∀ᵐ x ∂(P ∘ₘ π), ∀ y, (P†π) x {y} ≤ (P†π) x {f x}

variable {P : Kernel C 𝓧} [IsFiniteKernel P] {π : Measure C} [IsFiniteMeasure π] {f : 𝓧 → C}

/-- **A posterior argmax classifier is an argmin estimator for the 0-1 loss.** Let the set $C$ of
classes be countable and nonempty with measurable singletons, let $P$ be a finite kernel from $C$
to the observation space $\mathcal X$ and $\pi$ a finite measure on $C$, write $P \circ \pi$ for
the marginal measure on $\mathcal X$, $P^\dagger_\pi$ for the posterior kernel from $\mathcal X$
to $C$, and $\ell(c, y)$ for the 0-1 loss ($0$ if $y = c$, $1$ otherwise). If
$f : \mathcal X \to C$ is a posterior argmax classifier for $P$ and $\pi$, then $f$ is an argmin
estimator for $\ell$: it is measurable and, for $(P \circ \pi)$-almost every $x$,
$\int_C \ell(c, f(x))\,P^\dagger_\pi(x)(dc)$ equals
$\inf_{y \in C} \int_C \ell(c, y)\,P^\dagger_\pi(x)(dc)$. -/
theorem IsPosteriorArgmax.isArgminEstimator (hf : IsPosteriorArgmax P π f) :
    IsArgminEstimator zeroOneLoss P π f := by
  refine ⟨hf.measurable, ?_⟩
  filter_upwards [hf.ae_le] with x hx
  refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ _)
  rw [lintegral_zeroOneLoss_eq_one_sub, lintegral_zeroOneLoss_eq_one_sub]
  exact tsub_le_tsub_left (hx y) 1

/-- **Posterior argmax classifiers are exactly the argmin estimators for the 0-1 loss.** Let the
set $C$ of classes be countable and nonempty with measurable singletons, let $P$ be a finite
kernel from $C$ to the observation space $\mathcal X$ and $\pi$ a finite measure on $C$, write
$P \circ \pi$ for the marginal measure on $\mathcal X$, $P^\dagger_\pi$ for the posterior kernel
from $\mathcal X$ to $C$, and $\ell(c, y)$ for the 0-1 loss ($0$ if $y = c$, $1$ otherwise). A
map $f : \mathcal X \to C$ is a posterior argmax classifier for $P$ and $\pi$ if and only if it
is an argmin estimator for $\ell$: $f$ is measurable and, for $(P \circ \pi)$-almost every $x$,
$\int_C \ell(c, f(x))\,P^\dagger_\pi(x)(dc)$ equals
$\inf_{y \in C} \int_C \ell(c, y)\,P^\dagger_\pi(x)(dc)$. -/
theorem isPosteriorArgmax_iff_isArgminEstimator :
    IsPosteriorArgmax P π f ↔ IsArgminEstimator zeroOneLoss P π f := by
  refine ⟨IsPosteriorArgmax.isArgminEstimator, fun h => ⟨h.measurable, ?_⟩⟩
  filter_upwards [h.property] with x hx y
  have hle : ∫⁻ c, zeroOneLoss c (f x) ∂(P†π) x ≤ ∫⁻ c, zeroOneLoss c y ∂(P†π) x :=
    hx ▸ iInf_le _ y
  rw [lintegral_zeroOneLoss_eq_one_sub, lintegral_zeroOneLoss_eq_one_sub] at hle
  exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).mp hle

/-- **The Bayes classifier is optimal**: a posterior argmax classifier attains the Bayes risk
for the 0-1 loss. -/
theorem IsPosteriorArgmax.isBayesEstimator (hf : IsPosteriorArgmax P π f) :
    IsBayesEstimator zeroOneLoss P (Kernel.deterministic f hf.measurable) π :=
  hf.isArgminEstimator.isBayesEstimator measurable_zeroOneLoss

/-- **A posterior argmax classifier has minimal 0-1 risk.** Let the set $C$ of classes be countable
and nonempty with measurable singletons, let $P$ be a finite kernel from $C$ to the observation
space $\mathcal X$ and $\pi$ a finite measure on $C$, and let $\ell(c, y)$ be the 0-1 loss
($0$ if $y = c$, $1$ otherwise). For a kernel $\kappa$ from $\mathcal X$ to $C$, its average 0-1
risk is $\int_C \int_C \ell(c, y)\,(\kappa \circ P)(c)(dy)\,\pi(dc)$, where
$(\kappa \circ P)(c) = \int_{\mathcal X} \kappa(x)\,P(c)(dx)$. If $f : \mathcal X \to C$ is a
posterior argmax classifier for $P$ and $\pi$, then for every Markov kernel $\kappa$ from
$\mathcal X$ to $C$ (a randomized classifier), the average 0-1 risk of the deterministic kernel
$x \mapsto \delta_{f(x)}$ is at most the average 0-1 risk of $\kappa$. -/
theorem IsPosteriorArgmax.avgRisk_le (hf : IsPosteriorArgmax P π f) (κ : Kernel 𝓧 C)
    [IsMarkovKernel κ] :
    avgRisk zeroOneLoss P (Kernel.deterministic f hf.measurable) π ≤
      avgRisk zeroOneLoss P κ π := by
  rw [hf.isBayesEstimator]
  exact bayesRisk_le_avgRisk _ _ _ _

/-- **MAP classifiers are posterior argmax classifiers.** Let the set $C$ of classes be countable
and nonempty with measurable singletons, let the observation space $\mathcal X$ be countable with
measurable singletons, let $P$ be a Markov kernel from $C$ to $\mathcal X$ and $\pi$ a finite
measure on $C$, and write $P \circ \pi$ for the marginal measure on $\mathcal X$. If
$f : \mathcal X \to C$ assigns to every observation $x$ with $(P \circ \pi)(\{x\}) \ne 0$ a
maximum a posteriori class for $x$ under $P$ and $\pi$, then $f$ is a posterior argmax
classifier for $P$ and $\pi$.

Since posterior argmax classifiers attain the Bayes risk for the 0-1 loss, MAP classification is
Bayes optimal; observations of zero evidence may be classified arbitrarily. -/
theorem isPosteriorArgmax_of_isMAP [Countable 𝓧] [MeasurableSingletonClass 𝓧] [IsMarkovKernel P]
    (hf : ∀ x, (P ∘ₘ π) {x} ≠ 0 → Bayesian.IsMAP P π x (f x)) : IsPosteriorArgmax P π f := by
  refine ⟨measurable_of_countable f, ae_iff_of_countable.mpr fun x hx => ?_⟩
  exact (Bayesian.isMAP_iff_posterior P π hx (f x)).mp (hf x hx)

end Countable

section Finite

variable [Finite C] [MeasurableSingletonClass C] [Nonempty C]

/-- **Existence of a posterior argmax classifier.** Let the set $C$ of classes be finite and
nonempty with measurable singletons, let $P$ be a finite kernel from $C$ to the observation space
$\mathcal X$ and $\pi$ a finite measure on $C$. Then there is a posterior argmax classifier
$f : \mathcal X \to C$ for $P$ and $\pi$.

The classifier constructed takes, at each observation, the first maximizer of the posterior
probability in an enumeration of the classes. -/
theorem exists_isPosteriorArgmax (P : Kernel C 𝓧) [IsFiniteKernel P] (π : Measure C)
    [IsFiniteMeasure π] : ∃ f, IsPosteriorArgmax P π f := by
  classical
  have := Encodable.ofCountable C
  obtain ⟨c₀⟩ := ‹Nonempty C›
  let A : C → Set 𝓧 := fun y => {x | ∀ y', (P†π) x {y'} ≤ (P†π) x {y}}
  have hA : ∀ y, MeasurableSet (A y) := fun y => by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun y' => measurableSet_le
      ((P†π).measurable_coe (measurableSet_singleton y'))
      ((P†π).measurable_coe (measurableSet_singleton y))
  have hex : ∀ x, ∃ y, x ∈ A y := fun x =>
    (Finite.exists_max fun y => (P†π) x {y}).imp fun _ h => h
  let p : ℕ → 𝓧 → Prop := fun n x => ∃ y, Encodable.decode n = some y ∧ x ∈ A y
  have hp : ∀ n, MeasurableSet {x | p n x} := fun n => by
    cases h : (Encodable.decode n : Option C) with
    | none => simp [p, h]
    | some y => simpa [p, h] using hA y
  have hn : ∀ x, ∃ n, p n x := fun x => by
    obtain ⟨y, hy⟩ := hex x
    exact ⟨Encodable.encode y, y, Encodable.encodek y, hy⟩
  let g : ℕ → 𝓧 → C := fun n _ => (Encodable.decode n).getD c₀
  refine ⟨fun x => g (Nat.find (hn x)) x,
    ⟨Measurable.find (f := g) (fun _ => measurable_const) hp hn, ae_of_all _ fun x => ?_⟩⟩
  obtain ⟨y, hdec, hy⟩ := Nat.find_spec (hn x)
  simpa [g, hdec, A] using hy

/-- **The Bayes risk for the 0-1 loss.** Let the set $C$ of classes be finite and nonempty with
measurable singletons, let $P$ be a finite kernel from $C$ to the observation space $\mathcal X$
and $\pi$ a finite measure on $C$, and let $\ell(c, y)$ be the 0-1 loss ($0$ if $y = c$, $1$
otherwise). Write $P \circ \pi$ for the marginal measure on $\mathcal X$ and $P^\dagger_\pi$ for
the posterior kernel from $\mathcal X$ to $C$. For a kernel $\kappa$ from $\mathcal X$ to $C$,
write $(\kappa \circ P)(c) = \int_{\mathcal X} \kappa(x)\,P(c)(dx)$. Then the Bayes risk for the
0-1 loss, the infimum over all Markov kernels $\kappa$ from $\mathcal X$ to $C$ of the average
0-1 risk $\int_C \int_C \ell(c, y)\,(\kappa \circ P)(c)(dy)\,\pi(dc)$, equals
$\int_{\mathcal X} \inf_{y \in C} P^\dagger_\pi(x)(C \setminus \{y\})\,(P \circ \pi)(dx)$: the
average over the observations of the posterior probability of error of the best guess. -/
theorem bayesRisk_zeroOneLoss (P : Kernel C 𝓧) [IsFiniteKernel P] (π : Measure C)
    [IsFiniteMeasure π] :
    bayesRisk zeroOneLoss P π = ∫⁻ x, ⨅ y, (P†π) x {y}ᶜ ∂(P ∘ₘ π) := by
  obtain ⟨f, hf⟩ := exists_isPosteriorArgmax P π
  rw [HasArgminEstimator.bayesRisk_eq measurable_zeroOneLoss ⟨⟨f, hf.isArgminEstimator⟩⟩]
  simp_rw [lintegral_zeroOneLoss]

end Finite

end Cslib.MachineLearning.BayesClassifier
