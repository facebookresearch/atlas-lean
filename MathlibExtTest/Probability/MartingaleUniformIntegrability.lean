/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MartingaleUniformIntegrability

/-!
# Tests for uniform integrability and `L¹` convergence of (sub)martingales

Generic restatements of the public signatures in
`MathlibExt.Probability.MartingaleUniformIntegrability`, the
conditional-expectation martingale of an integrable random variable as a
concrete uniformly integrable martingale, and the `L¹`-convergence-implies-
uniform-integrability direction for submartingales.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MathlibExtTest.Probability.MartingaleUniformIntegrability

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The submartingale three-way equivalence restates with the exact public signature. -/
example (hsub : Submartingale X ℱ μ) :
    List.TFAE [
      UniformIntegrable X 1 μ,
      ∃ X_inf, Integrable X_inf μ ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (X_inf ω))) ∧
        Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧
        Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0)
    ] :=
  hsub.uniformIntegrable_tfae

/-- The martingale four-way equivalence restates with the exact public signature. -/
example (hmart : Martingale X ℱ μ) :
    List.TFAE [
      UniformIntegrable X 1 μ,
      ∃ X_inf, Integrable X_inf μ ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (X_inf ω))) ∧
        Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧
        Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧ ∀ n, X n =ᵐ[μ] μ[X_inf | ℱ n]
    ] :=
  hmart.uniformIntegrable_tfae

/-- The conditional-expectation martingale of an integrable `g` is uniformly
integrable: it satisfies the fourth condition of the martingale equivalence
with `X_∞ = g` (by reflexivity of `=ᵐ[μ]`). -/
example {g : Ω → ℝ} (hg : Integrable g μ) :
    UniformIntegrable (fun n => μ[g | ℱ n]) 1 μ := by
  have hmart : Martingale (fun n => μ[g | ℱ n]) ℱ μ := martingale_condExp g ℱ μ
  refine (hmart.uniformIntegrable_tfae.out 4 1).mp ?_
  exact ⟨g, hg, fun n => EventuallyEq.rfl⟩

/-- A submartingale converging in `L¹` is uniformly integrable (the
`3 → 1` direction of the submartingale equivalence). -/
example (hsub : Submartingale X ℱ μ)
    {X_inf : Ω → ℝ} (hint : Integrable X_inf μ)
    (hL1 : Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0)) :
    UniformIntegrable X 1 μ := by
  refine (hsub.uniformIntegrable_tfae.out 3 1).mp ?_
  exact ⟨X_inf, hint, hL1⟩

/-- A uniformly integrable martingale converges almost surely and in `L¹`
to some integrable limit (the `1 → 2` direction). -/
example (hmart : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∃ X_inf, Integrable X_inf μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (X_inf ω))) ∧
      Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0) :=
  (hmart.uniformIntegrable_tfae.out 1 2).mp hUI

/-- A uniformly integrable submartingale converges in `L¹` to some
integrable limit (the `1 → 3` direction, via the a.e. form). -/
example (hsub : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∃ X_inf, Integrable X_inf μ ∧
      Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) atTop (nhds 0) :=
  (hsub.uniformIntegrable_tfae.out 1 3).mp hUI

#print axioms MeasureTheory.Submartingale.uniformIntegrable_tfae
#print axioms MeasureTheory.Martingale.uniformIntegrable_tfae

end MathlibExtTest.Probability.MartingaleUniformIntegrability
