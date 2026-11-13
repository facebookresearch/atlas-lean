/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Basic
public import MathlibExt.Algebra.BigOperators.ProdCompPow
public import MathlibExt.Probability.Distributions.Dirichlet

/-!
# Dirichlet–multinomial conjugacy

The parameter `θ` is a probability vector over `n + 1` labels. The data are `N` independent
labels `s : Fin N → Fin (n + 1)` drawn from `θ` (`categoricalSeqKernel`), and the prior is the
Dirichlet distribution `Dir(α)` (MathlibExt's `dirichletMeasure`).

* `seqLikelihood_eq_prod_pow`: the likelihood `∏ₘ θ (s m)` depends on the data only through the
  counts, as `∏ᵢ θᵢ ^ nᵢ`.
* `posterior_categoricalSeqKernel_dirichletMeasure` (**conjugacy**): the posterior after observing
  `s` is `Dir(α + n)`, where `nᵢ` is the number of occurrences of label `i`.
* `posterior_predictive_dirichletMeasure` (**posterior predictive**): the next label is `i` with
  probability `(αᵢ + nᵢ) / (∑ α + N)`. For `α = 1` this is add-one (Laplace) smoothing.

For concentrations `αᵢ ≥ 1` the posterior mode (MAP estimate) is `mapEstimate` in
`CSLibExt/MachineLearning/Generative/Categorical.lean`: the normalized pseudo-counts
`nᵢ + αᵢ - 1`, i.e. add-`(α - 1)` smoothing. The posterior predictive below is add-`α` smoothing.

Parameters outside the probability vectors are a `Dir(α)`-null set. There the kernels draw a
fixed label, which keeps them Markov.

## References

* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §2.2.1.
* K. P. Murphy, *Machine Learning: A Probabilistic Perspective*, MIT Press, 2012, §3.4.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n N : ℕ}

/-- **Probability vectors.** For $n \in \mathbb{N}$, the probability vectors are the
$\theta \in \mathbb{R}^{n+1}$ with $\theta_i \ge 0$ for every $i$ and $\sum_i \theta_i = 1$; they
form the parameter space of the categorical model. -/
def probVectors (n : ℕ) : Set (Fin (n + 1) → ℝ) := {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1}

theorem measurableSet_probVectors (n : ℕ) : MeasurableSet (probVectors n) := by
  have h1 : MeasurableSet {θ : Fin (n + 1) → ℝ | ∀ i, 0 ≤ θ i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {θ : Fin (n + 1) → ℝ | ∑ i, θ i = 1} :=
    measurableSet_eq_fun (f := fun θ : Fin (n + 1) → ℝ ↦ ∑ i, θ i) (by fun_prop) measurable_const
  exact h1.inter h2

private theorem sum_smul_dirac_singleton {𝓨 : Type*} [Fintype 𝓨] [MeasurableSpace 𝓨]
    [MeasurableSingletonClass 𝓨] (w : 𝓨 → ℝ≥0∞) (y : 𝓨) :
    (∑ y', w y' • Measure.dirac y') {y} = w y := by
  classical
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton y), Ne.symm hb]
  · simp

private theorem sum_smul_dirac_univ {𝓨 : Type*} [Fintype 𝓨] [MeasurableSpace 𝓨]
    (w : 𝓨 → ℝ≥0∞) : (∑ y', w y' • Measure.dirac y') Set.univ = ∑ y, w y := by
  simp

open scoped Classical in
/-- **The categorical likelihood.** For $n \in \mathbb{N}$, the categorical likelihood is the
kernel from parameters $\theta \in \mathbb{R}^{n+1}$ to labels $\{0, \dots, n\}$ that sends a
probability vector $\theta$ (all $\theta_i \ge 0$ and $\sum_i \theta_i = 1$) to the law of one
label drawn with probability $\theta_i$ for label $i$, and sends every other $\theta$ to the
point mass at label $0$.

Parameters outside the probability vectors form a null set under a Dirichlet prior. -/
noncomputable def categoricalKernel (n : ℕ) : Kernel (Fin (n + 1) → ℝ) (Fin (n + 1)) :=
  Kernel.piecewise (measurableSet_probVectors n)
    ⟨fun θ ↦ ∑ i, ENNReal.ofReal (θ i) • Measure.dirac i,
      Measure.measurable_of_measurable_coe _ fun A _ ↦ by
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
        exact Finset.measurable_sum _ fun i _ ↦
          (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul_const _⟩
    (Kernel.const _ (Measure.dirac 0))

/-- **Likelihood of a label sequence.** For $\theta \in \mathbb{R}^{n+1}$ and a sequence
$s = (s_0, \dots, s_{N-1})$ of labels in $\{0, \dots, n\}$, the likelihood of $s$ is the
extended nonnegative real $\prod_{m < N} \theta_{s_m}^+$, where $x^+ = \max(x, 0)$. -/
noncomputable def seqLikelihood (θ : Fin (n + 1) → ℝ) (s : Fin N → Fin (n + 1)) : ℝ≥0∞ :=
  ∏ m, ENNReal.ofReal (θ (s m))

theorem measurable_seqLikelihood (s : Fin N → Fin (n + 1)) :
    Measurable fun θ : Fin (n + 1) → ℝ ↦ seqLikelihood θ s :=
  Finset.measurable_prod _ fun _ _ ↦ ENNReal.measurable_ofReal.comp (measurable_pi_apply _)

open scoped Classical in
/-- **The multinomial sampling model.** For $n, N \in \mathbb{N}$, the multinomial sampling
model is the kernel from parameters $\theta \in \mathbb{R}^{n+1}$ to sequences
$s = (s_0, \dots, s_{N-1})$ of $N$ labels in $\{0, \dots, n\}$ that sends a probability vector
$\theta$ (all $\theta_i \ge 0$ and $\sum_i \theta_i = 1$) to the law of $N$ independent draws
from $\theta$, which gives $s$ probability $\prod_{m < N} \theta_{s_m}$, and sends every other
$\theta$ to the point mass at the all-zero sequence. -/
noncomputable def categoricalSeqKernel (n N : ℕ) :
    Kernel (Fin (n + 1) → ℝ) (Fin N → Fin (n + 1)) :=
  Kernel.piecewise (measurableSet_probVectors n)
    ⟨fun θ ↦ ∑ s, seqLikelihood θ s • Measure.dirac s,
      Measure.measurable_of_measurable_coe _ fun A _ ↦ by
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
        exact Finset.measurable_sum _ fun s _ ↦ (measurable_seqLikelihood s).mul_const _⟩
    (Kernel.const _ (Measure.dirac fun _ : Fin N ↦ (0 : Fin (n + 1))))

private theorem sum_ofReal_of_mem_probVectors {θ : Fin (n + 1) → ℝ}
    (hθ : θ ∈ probVectors n) : ∑ i, ENNReal.ofReal (θ i) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hθ.1 i, hθ.2, ENNReal.ofReal_one]

instance : IsMarkovKernel (categoricalKernel n) := by
  classical
  refine ⟨fun θ ↦ ⟨?_⟩⟩
  rw [categoricalKernel, Kernel.piecewise_apply]
  split_ifs with hθ
  · exact (sum_smul_dirac_univ _).trans (sum_ofReal_of_mem_probVectors hθ)
  · simp

instance : IsMarkovKernel (categoricalSeqKernel n N) := by
  classical
  refine ⟨fun θ ↦ ⟨?_⟩⟩
  rw [categoricalSeqKernel, Kernel.piecewise_apply]
  split_ifs with hθ
  · refine (sum_smul_dirac_univ _).trans ?_
    simp only [seqLikelihood]
    rw [← Fintype.prod_sum (fun _ i ↦ ENNReal.ofReal (θ i))]
    simp [sum_ofReal_of_mem_probVectors hθ]
  · simp

theorem categoricalKernel_apply {θ : Fin (n + 1) → ℝ} (hθ : θ ∈ probVectors n) (i : Fin (n + 1)) :
    categoricalKernel n θ {i} = ENNReal.ofReal (θ i) := by
  classical
  simp only [categoricalKernel, Kernel.piecewise_apply, hθ, ↓reduceIte]
  exact sum_smul_dirac_singleton _ i

theorem categoricalSeqKernel_apply {θ : Fin (n + 1) → ℝ} (hθ : θ ∈ probVectors n)
    (s : Fin N → Fin (n + 1)) : categoricalSeqKernel n N θ {s} = seqLikelihood θ s := by
  classical
  simp only [categoricalSeqKernel, Kernel.piecewise_apply, hθ, ↓reduceIte]
  exact sum_smul_dirac_singleton _ s

/-- **Label counts.** For a sequence $s = (s_0, \dots, s_{N-1})$ of labels in $\{0, \dots, n\}$
and a label $i$, the count $n_i(s)$ is the number of positions $m < N$ with $s_m = i$. -/
def counts (s : Fin N → Fin (n + 1)) (i : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter fun m ↦ s m = i).card

theorem sum_counts (s : Fin N → Fin (n + 1)) : ∑ i, counts s i = N := by
  simp only [counts]
  rw [← Finset.card_eq_sum_card_fiberwise (fun m _ ↦ Finset.mem_univ (s m)), Finset.card_univ,
    Fintype.card_fin]

/-- **The sequence likelihood depends only on the label counts.** For every
$\theta \in \mathbb{R}^{n+1}$ and every sequence $s$ of $N$ labels in $\{0, \dots, n\}$ with
label counts $n_i(s)$, the likelihood $\prod_{m < N} \theta_{s_m}^+$ of $s$ equals
$\prod_{i = 0}^{n} (\theta_i^+)^{n_i(s)}$ as extended nonnegative reals, where
$x^+ = \max(x, 0)$. -/
theorem seqLikelihood_eq_prod_pow (θ : Fin (n + 1) → ℝ) (s : Fin N → Fin (n + 1)) :
    seqLikelihood θ s = ∏ i, ENNReal.ofReal (θ i) ^ counts s i := by
  classical
  simpa [seqLikelihood, counts] using Fintype.prod_comp_eq_prod_pow s fun i ↦ ENNReal.ofReal (θ i)

/-! ### Conjugacy -/

section Conjugacy

variable {α : Fin (n + 1) → ℝ}

theorem ae_mem_probVectors (α : Fin (n + 1) → ℝ) :
    ∀ᵐ θ ∂dirichletMeasure α, θ ∈ probVectors n := by
  filter_upwards [ae_dirichletMeasure α] with θ hθ
  exact ⟨fun i ↦ (hθ.1 i).le, hθ.2⟩

/-- **Evidence-weighted Dirichlet prior.** Let $\alpha \in \mathbb{R}^{n+1}$ with $\alpha_i > 0$
for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$ with label counts
$n_i(s)$. The Dirichlet distribution $\mathrm{Dir}(\alpha)$ weighted by the density
$\theta \mapsto P_\theta(s)$, the probability of $s$ under the multinomial sampling model with
parameter $\theta$, equals $B(\alpha + n(s)) / B(\alpha)$ times $\mathrm{Dir}(\alpha + n(s))$,
where $B$ is the multivariate Beta function and $\alpha + n(s)$ has entries $\alpha_i + n_i(s)$. -/
theorem withDensity_categoricalSeqKernel (hα : ∀ i, 0 < α i) (s : Fin N → Fin (n + 1)) :
    (dirichletMeasure α).withDensity (fun θ ↦ categoricalSeqKernel n N θ {s}) =
      ENNReal.ofReal (multiBeta (fun i ↦ α i + counts s i) / multiBeta α) •
        dirichletMeasure (fun i ↦ α i + counts s i) := by
  rw [← withDensity_prod_pow_dirichletMeasure hα]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_mem_probVectors α] with θ hθ
  rw [categoricalSeqKernel_apply hθ, seqLikelihood_eq_prod_pow]

/-- **Dirichlet–multinomial conjugacy.** Let $\alpha \in \mathbb{R}^{n+1}$ with $\alpha_i > 0$
for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$ with label counts
$n_i(s)$. Under the multinomial sampling model with the Dirichlet prior $\mathrm{Dir}(\alpha)$,
the posterior distribution of the parameter after observing $s$ is the Dirichlet distribution
with parameters $\alpha_i + n_i(s)$. -/
theorem posterior_categoricalSeqKernel_dirichletMeasure (hα : ∀ i, 0 < α i)
    (s : Fin N → Fin (n + 1)) :
    haveI := isProbabilityMeasure_dirichletMeasure hα
    ((categoricalSeqKernel n N)†(dirichletMeasure α)) s =
      dirichletMeasure (fun i ↦ α i + counts s i) := by
  have := isProbabilityMeasure_dirichletMeasure hα
  have hαk : ∀ i, 0 < α i + counts s i := fun i ↦ by have := hα i; positivity
  have := isProbabilityMeasure_dirichletMeasure hαk
  have hc : 0 < multiBeta (fun i ↦ α i + counts s i) / multiBeta α :=
    div_pos (multiBeta_pos hαk (Nat.succ_ne_zero n)) (multiBeta_pos hα (Nat.succ_ne_zero n))
  have hev : (categoricalSeqKernel n N ∘ₘ dirichletMeasure α) {s} =
      ENNReal.ofReal (multiBeta (fun i ↦ α i + counts s i) / multiBeta α) := by
    rw [← withDensity_univ_eq_comp, withDensity_categoricalSeqKernel hα, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
  have hev0 : (categoricalSeqKernel n N ∘ₘ dirichletMeasure α) {s} ≠ 0 := by
    rw [hev]
    exact (ENNReal.ofReal_pos.mpr hc).ne'
  rw [posterior_eq_bayesPosterior _ _ hev0, bayesPosterior, withDensity_categoricalSeqKernel hα,
    hev, smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top,
    one_smul]

/-- **Prior predictive of the Dirichlet–categorical model.** Let $\alpha \in \mathbb{R}^{n+1}$
with $\alpha_i > 0$ for every $i$. Drawing a parameter $\theta$ from the Dirichlet
distribution $\mathrm{Dir}(\alpha)$ and then one label from the categorical likelihood with
parameter $\theta$ gives the label $i \in \{0, \dots, n\}$ with probability
$\alpha_i / \sum_j \alpha_j$, which is the mean of $\theta_i$ under $\mathrm{Dir}(\alpha)$. -/
theorem categoricalKernel_comp_dirichletMeasure (hα : ∀ i, 0 < α i) (i : Fin (n + 1)) :
    (categoricalKernel n ∘ₘ dirichletMeasure α) {i} = ENNReal.ofReal (α i / ∑ j, α j) := by
  rw [comp_apply_singleton, ← lintegral_dirichletMeasure_apply hα i]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_probVectors α] with θ hθ
  rw [categoricalKernel_apply hθ]

/-- **Posterior predictive of the Dirichlet–multinomial model.** Let $\alpha \in \mathbb{R}^{n+1}$
with $\alpha_i > 0$ for every $i$, and let $s$ be a sequence of $N$ labels in $\{0, \dots, n\}$
with label counts $n_i(s)$. Under the multinomial sampling model with the Dirichlet prior
$\mathrm{Dir}(\alpha)$, drawing a parameter from the posterior after observing $s$ and then one
label from the categorical likelihood gives the label $i$ with probability
$(\alpha_i + n_i(s)) / (\sum_j \alpha_j + N)$.

This is the Dirichlet–multinomial analogue of Laplace's rule of succession. -/
theorem posterior_predictive_dirichletMeasure (hα : ∀ i, 0 < α i) (s : Fin N → Fin (n + 1))
    (i : Fin (n + 1)) :
    haveI := isProbabilityMeasure_dirichletMeasure hα
    (categoricalKernel n ∘ₘ ((categoricalSeqKernel n N)†(dirichletMeasure α)) s) {i} =
      ENNReal.ofReal ((α i + counts s i) / (∑ j, α j + N)) := by
  have := isProbabilityMeasure_dirichletMeasure hα
  have hαk : ∀ j, 0 < α j + counts s j := fun j ↦ by have := hα j; positivity
  rw [posterior_categoricalSeqKernel_dirichletMeasure hα s,
    categoricalKernel_comp_dirichletMeasure hαk, Finset.sum_add_distrib]
  congr 3
  exact_mod_cast sum_counts s

end Conjugacy

end Cslib.MachineLearning.Bayesian
