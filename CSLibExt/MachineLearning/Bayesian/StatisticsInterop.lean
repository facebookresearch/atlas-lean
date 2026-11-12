/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.NormalNormal
public import CSLibExt.MachineLearning.Bayesian.DirichletMultinomial
import Mathlib.Probability.ProductMeasure
public import CSLibExt.MachineLearning.Bayesian.Basic
public import MathlibExt.Probability.Statistics.Bayesian.FiniteConsistency

@[expose] public section

/-! # Normal-normal posterior, one-draw marginal form

The one-draw marginal law coincides with the Gaussian likelihood. The posterior below is a
restatement of the normal-normal posterior for that marginal law; its kernel and evidence
are the likelihood's own (no separate posterior object is constructed). -/

/-! # Dirichlet-multinomial posterior on the shared sampling law

The `N`-sample categorical kernel coincides with the iid tuple law on probability
vectors, and the Dirichlet posterior of that shared object is the displayed update. -/

/-! # Finite-model posterior weights as a kernel posterior

The explicit finite-model posterior weights equal the `toReal` of the Bayes posterior of
a product likelihood kernel against a counting-weighted prior. -/

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **One-draw marginal law.** The pushforward of the one-observation iid Gaussian tuple law
along evaluation equals the Gaussian likelihood, at every noise variance including `v = 0`
(where both sides are the Dirac mass at `θ`). -/
theorem gaussianMarginalLaw_one_eq_gaussianLikelihood (θ : ℝ) {v : ℝ≥0} :
    (Measure.pi fun _ : Fin 1 => gaussianReal θ v).map (fun s => s 0) =
      gaussianLikelihood v θ := by
  by_cases h : v = 0
  · subst h
    rw [gaussianLikelihood_zero_apply θ]
    exact (measurePreserving_eval (fun _ : Fin 1 => gaussianReal θ 0) 0).map_eq
  · rw [gaussianLikelihood_apply h]
    exact (measurePreserving_eval (fun _ : Fin 1 => gaussianReal θ v) 0).map_eq

/-- **Normal-Normal posterior, marginal form.** Under a `N(m₀, v₀)` prior with `v₀ ≠ 0` and
noise variance `v ≠ 0`, the a.e. posterior restatement for the one-draw marginal law is the
candidate posterior kernel. This is `posterior_gaussianLikelihood_gaussianReal` applied to the
one-observation marginal; no new posterior kernel or evidence object is constructed. -/
theorem posterior_gaussianMarginalLaw_one (m₀ : ℝ) {v₀ v : ℝ≥0} [NeZero v₀] [NeZero v] :
    ∀ᵐ x ∂(gaussianLikelihood v ∘ₘ gaussianReal m₀ v₀),
      ((gaussianLikelihood v)†(gaussianReal m₀ v₀)) x =
        normalPosteriorKernel m₀ v₀ v x := by
  have h₀ : v₀ ≠ 0 := NeZero.ne v₀
  have h : v ≠ 0 := NeZero.ne v
  rw [gaussianLikelihood_comp_gaussianReal m₀ h₀ h]
  have hac : gaussianReal m₀ (v₀ + v) ≪ volume :=
    gaussianReal_absolutelyContinuous m₀ (by positivity)
  have hae := hac (posterior_gaussianLikelihood_gaussianReal m₀ (v₀ := v₀) (v := v))
  filter_upwards [hae] with x hx
  rw [hx, normalPosteriorKernel_apply m₀ h₀ h x]

/-- **Categorical sequence kernel as product law.** On probability vectors, the categorical
`N`-sample kernel equals the iid product of the one-draw categorical kernel. -/
theorem categoricalSeqKernel_eq_pi_categoricalKernel (n N : ℕ) (θ : Fin (n + 1) → ℝ)
    (hθ : θ ∈ probVectors n) :
    categoricalSeqKernel n N θ = Measure.pi fun _ : Fin N => categoricalKernel n θ := by
  rw [Measure.ext_iff_singleton]
  intro s
  rw [categoricalSeqKernel_apply hθ, Measure.pi_singleton]
  simp only [categoricalKernel_apply hθ]
  rfl

/-- **Dirichlet posterior of the shared law, `bayesPosterior` form.** The posterior of the
shared sample-law object at the observed labels is the displayed Dirichlet update. -/
theorem posterior_sharedSeqLaw_bayesPosterior (n N : ℕ) (α : Fin (n + 1) → ℝ)
    (hα : ∀ i, 0 < α i) (s : Fin N → Fin (n + 1)) :
    bayesPosterior (categoricalSeqKernel n N) (dirichletMeasure α) s =
      dirichletMeasure (fun i => α i + counts s i) := by
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
  rw [← posterior_eq_bayesPosterior _ _ hev0]
  exact posterior_categoricalSeqKernel_dirichletMeasure hα s

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Finite-model weights are the kernel posterior.** The explicit posterior weights
`postWeight` of the merged finite-model consistency theorem equal the `toReal` of the kernel
posterior `bayesPosterior` of any product likelihood kernel against any counting-weighted prior. -/
theorem postWeight_eq_bayesPosterior {Θ 𝓧 : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype 𝓧] [MeasurableSpace Θ] [Countable Θ] [MeasurableSingletonClass Θ]
    [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]
    (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ) (f : Θ → 𝓧 → ℝ) (hf : ∀ θ x, 0 ≤ f θ x)
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → 𝓧) (n : ℕ) (ω : Ω) (θ : Θ)
    (μ : Measure Θ) (hμ : ∀ θ, μ {θ} = ENNReal.ofReal (π θ))
    (K : Kernel Θ (Fin n → 𝓧))
    (hK : ∀ θ (s : Fin n → 𝓧), K θ {s} = ∏ i, ENNReal.ofReal (f θ (s i))) :
    MathlibExt.Probability.Statistics.Bayesian.postWeight π f X n ω θ =
      (bayesPosterior K μ (fun i => X i ω) {θ}).toReal := by
  have hprod_nonneg : ∀ θ' : Θ, 0 ≤ ∏ i ∈ Finset.range n, f θ' (X i ω) :=
    fun θ' => Finset.prod_nonneg (fun i _ => hf θ' (X i ω))
  have hterm_nonneg : ∀ θ' : Θ, 0 ≤ π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω) :=
    fun θ' => mul_nonneg (hπ θ') (hprod_nonneg θ')
  have hterm : ∀ θ' : Θ, ENNReal.ofReal (π θ') * ∏ i : Fin n, ENNReal.ofReal (f θ' (X ↑i ω)) =
      ENNReal.ofReal (π θ' * ∏ i ∈ Finset.range n, f θ' (X i ω)) := by
    intro θ'
    rw [← ENNReal.ofReal_prod_of_nonneg (fun (i : Fin n) _ => hf θ' (X ↑i ω))]
    rw [Fin.prod_univ_eq_prod_range (fun j => f θ' (X j ω)) n]
    rw [← ENNReal.ofReal_mul (hπ θ')]
  rw [bayesPosterior_apply_singleton]
  simp only [hμ, hK, hterm, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun θ' _ => hterm_nonneg θ')]
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (hterm_nonneg θ),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun θ' _ => hterm_nonneg θ'))]
  rfl

end Cslib.MachineLearning.Bayesian
