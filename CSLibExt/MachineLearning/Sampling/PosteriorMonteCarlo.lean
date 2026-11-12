/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MonteCarlo
public import CSLibExt.MachineLearning.Bayesian.Basic
public import MathlibExt.Probability.MonteCarloRate

/-!
# Monte Carlo error for exact posterior draws

* `variance_mcEstimate`: for mutually independent draws with common law `ν` and a measurable
  `f ∈ L²(ν)`, the Monte Carlo average of `m > 0` draws has variance `Var_ν(f) / m`.
* `mcEstimate_bayesPosterior_mean_variance`: for exact independent draws from the Bayes posterior
  `bayesPosterior κ π x` (positive evidence), the Monte Carlo average is unbiased for the posterior
  mean (statistical target) and has variance `Var_posterior(g) / m` (Monte Carlo error).

Only exact i.i.d. draws are covered; no Markov chain Monte Carlo statement is made.

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, §3.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open MeasureTheory ProbabilityTheory

/-- **Monte Carlo variance.** For mutually independent draws `X i` with common law `ν` and a
measurable square-integrable integrand `f`, the Monte Carlo average of `m > 0` draws has variance
`Var_ν(f) / m`.

Source: C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., §3.2. -/
theorem variance_mcEstimate {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {ν : Measure α} {f : α → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 ν)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν)
    (hind : iIndepFun X μ) {m : ℕ} (hm : m ≠ 0) :
    variance (mcEstimate f X m) μ = variance f ν / m := by
  have hident : ∀ i, IdentDistrib (fun ω ↦ f (X i ω)) (fun ω ↦ f (X 0 ω)) μ μ := fun i ↦
    (IdentDistrib.mk (hX i).aemeasurable (hX 0).aemeasurable (by rw [hlaw i, hlaw 0])).comp hf
  have hmem : MemLp (fun ω ↦ f (X 0 ω)) 2 μ := by
    rw [← hlaw 0] at hf2
    exact hf2.comp_of_map (hX 0).aemeasurable
  have hvar : variance f ν = variance (fun ω ↦ f (X 0 ω)) μ := by
    rw [← hlaw 0]
    exact variance_map hf.aemeasurable (hX 0).aemeasurable
  have hshape : mcEstimate f X m = fun ω ↦ (∑ i ∈ Finset.range m, f (X i ω)) / (m : ℝ) := by
    funext ω
    rw [mcEstimate, div_eq_inv_mul]
  rw [hshape, MathlibExt.Probability.variance_sample_mean_of_iid (fun i ω ↦ f (X i ω))
    (hind.comp (fun _ ↦ f) fun _ ↦ hf) hident hmem m hm, hvar]

/-- **Posterior Monte Carlo: statistical target and sampling error.** Draw `θs 0, θs 1, …`
independently from the Bayes posterior `bayesPosterior κ π x` (positive evidence at `x`). For a
measurable `g` square-integrable under the posterior, the Monte Carlo average of `m > 0` draws is
unbiased for the posterior mean `∫ g d(posterior)` and has variance `Var_posterior(g) / m`. -/
theorem mcEstimate_bayesPosterior_mean_variance {Θ 𝓧 Ω : Type*} [MeasurableSpace Θ]
    [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] [MeasurableSpace Ω] {μ : Measure Ω}
    (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (π : Measure Θ) [IsFiniteMeasure π] {x : 𝓧}
    (hx : (κ ∘ₘ π) {x} ≠ 0) {g : Θ → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (Cslib.MachineLearning.Bayesian.bayesPosterior κ π x))
    {θs : ℕ → Ω → Θ} (hθs : ∀ i, Measurable (θs i))
    (hlaw : ∀ i, μ.map (θs i) = Cslib.MachineLearning.Bayesian.bayesPosterior κ π x)
    (hind : iIndepFun θs μ) {m : ℕ} (hm : m ≠ 0) :
    (∫ ω, mcEstimate g θs m ω ∂μ =
        ∫ θ, g θ ∂Cslib.MachineLearning.Bayesian.bayesPosterior κ π x) ∧
      variance (mcEstimate g θs m) μ =
        variance g (Cslib.MachineLearning.Bayesian.bayesPosterior κ π x) / m := by
  have := Cslib.MachineLearning.Bayesian.isProbabilityMeasure_bayesPosterior κ π hx
  exact ⟨integral_mcEstimate hg (hg2.integrable one_le_two) hθs hlaw hm,
    variance_mcEstimate hg hg2 hθs hlaw hind hm⟩

end Cslib.MachineLearning.Sampling
