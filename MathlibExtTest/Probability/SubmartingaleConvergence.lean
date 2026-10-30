/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SubmartingaleConvergence

@[expose] public section

open MeasureTheory Filter Topology

namespace MathlibExtTest.Probability.SubmartingaleConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-- Expectations are monotone along the constant submartingale: both sides equal `c`. -/
example (c : ℝ) {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, (fun _ _ => c) i ω ∂μ ≤ ∫ ω, (fun _ _ => c) j ω ∂μ :=
  Submartingale.integral_mono (martingale_const ℱ μ c).submartingale hij

/-- The `L¹` bound is an identity for a constant submartingale: `‖c‖ = 2 c⁺ - c`. -/
example (c : ℝ) (n : ℕ) :
    ∫ ω, ‖(fun _ _ => c) n ω‖ ∂μ ≤ 2 * (c)⁺ - ∫ ω, (fun _ _ => c) 0 ω ∂μ :=
  Submartingale.integral_norm_le (C := (c)⁺)
    (martingale_const ℱ μ c).submartingale (fun k => by simp) n

/-- A constant process converges almost surely (to the constant itself), via the
submartingale convergence theorem. -/
example (c : ℝ) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (fun _ _ => c) n ω) atTop (𝓝 (X_inf ω)) :=
  Submartingale.exists_ae_tendsto_of_posPart_bdd (C := (c)⁺)
    (martingale_const ℱ μ c).submartingale (fun k => by simp)

/-- A constant process converges almost surely, via the supermartingale form
(bound on the negative parts). -/
example (c : ℝ) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (fun _ _ => c) n ω) atTop (𝓝 (X_inf ω)) :=
  Supermartingale.exists_ae_tendsto_of_negPart_bdd (C := (c)⁻)
    (martingale_const ℱ μ c).supermartingale (fun k => by simp)

/-- The conditional-expectation martingale `n ↦ E[g | ℱ n]` converges almost surely:
its positive parts satisfy `∫ (E[g | ℱ n])⁺ ≤ ∫ ‖g‖`, since `(x)⁺ ≤ ‖x‖` and
conditional expectation contracts `L¹` norms. -/
example [SigmaFiniteFiltration μ ℱ] (g : Ω → ℝ) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop (𝓝 (X_inf ω)) := by
  apply Martingale.exists_ae_tendsto_of_posPart_bdd (martingale_condExp g ℱ μ)
  intro n
  calc ∫ ω, (μ[g | ℱ n] ω)⁺ ∂μ
      ≤ ∫ ω, ‖μ[g | ℱ n] ω‖ ∂μ := by
        apply integral_mono_ae _ (integrable_condExp.norm) _
        · exact (integrable_condExp.sup (integrable_zero _ _ μ))
        · filter_upwards with ω
          exact max_le (le_abs_self _) (abs_nonneg _)
    _ ≤ ∫ ω, ‖g ω‖ ∂μ := integral_norm_condExp_le g

end MathlibExtTest.Probability.SubmartingaleConvergence
