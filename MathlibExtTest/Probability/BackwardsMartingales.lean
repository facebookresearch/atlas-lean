/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BackwardsMartingales

@[expose] public section

open MeasureTheory Filter

open scoped Topology

namespace MathlibExtTest.Probability.BackwardsMartingales

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Restatement of Lévy's downward theorem (a.s. form). -/
example {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 ((μ[g | ⨅ n, m n]) ω)) :=
  MeasureTheory.levy_downward_ae m hm hm0

/-- Restatement of Lévy's downward theorem (`L¹` form). -/
example {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (hg : Integrable g μ) :
    Tendsto (fun n => eLpNorm ((μ[g | m n]) - μ[g | ⨅ n, m n]) 1 μ) atTop (𝓝 0) :=
  MeasureTheory.levy_downward_tendsto_eLpNorm_one m hm hm0 hg

/-- The constant family `m n = ⊥` is a decreasing sequence of
sub-σ-algebras, so Lévy's downward theorem applies to it: the conditional
expectations `μ[g | ⊥]` (constant in `n`) converge a.e. to
`μ[g | ⨅ n, ⊥]`. -/
example {g : Ω → ℝ} :
    ∀ᵐ ω ∂μ, Tendsto (fun _n : ℕ => (μ[g | (⊥ : MeasurableSpace Ω)]) ω) atTop
      (𝓝 ((μ[g | ⨅ _n : ℕ, (⊥ : MeasurableSpace Ω)]) ω)) :=
  MeasureTheory.levy_downward_ae (fun _ => (⊥ : MeasurableSpace Ω)) (fun _ _ _ => le_rfl)
    (fun _ => bot_le)

/-- Restatement of backwards martingale convergence (a.s. form). -/
example {M : ℕ → Ω → ℝ} (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (hM : MeasureTheory.IsBackwardsMartingale M m μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 ((μ[M 0 | ⨅ n, m n]) ω)) :=
  MeasureTheory.backwards_martingale_ae_tendsto m hm hm0 hM

/-- Restatement of backwards martingale convergence (`L¹` form). -/
example {M : ℕ → Ω → ℝ} (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (hM : MeasureTheory.IsBackwardsMartingale M m μ) :
    Tendsto (fun n => eLpNorm (M n - μ[M 0 | ⨅ n, m n]) 1 μ) atTop (𝓝 0) :=
  MeasureTheory.backwards_martingale_tendsto_eLpNorm_one m hm hm0 hM

/-- The conditional expectations `n ↦ μ[g | m n]` form a backwards
martingale: the `0`-th term is integrable, and each term is the
conditional expectation of the `0`-th term. -/
example {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) :
    MeasureTheory.IsBackwardsMartingale (fun n => μ[g | m n]) m μ := by
  refine ⟨integrable_condExp, fun n => ?_⟩
  show (μ[g | m n]) =ᵐ[μ] μ[μ[g | m 0] | m n]
  have hSF : SigmaFinite (μ.trim (hm0 n)) := inferInstance
  exact (condExp_condExp_of_le (hm (Nat.zero_le n)) (hm0 0)).symm

#print axioms MeasureTheory.levy_downward_ae
#print axioms MeasureTheory.levy_downward_tendsto_eLpNorm_one
#print axioms MeasureTheory.backwards_martingale_ae_tendsto
#print axioms MeasureTheory.backwards_martingale_tendsto_eLpNorm_one

end MathlibExtTest.Probability.BackwardsMartingales
