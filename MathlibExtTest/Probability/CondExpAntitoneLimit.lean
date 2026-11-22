/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CondExpAntitoneLimit

@[expose] public section

open MeasureTheory Filter
open scoped Topology MeasureTheory

namespace MathlibExtTest.Probability.CondExpAntitoneLimit

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Constant filtration: the conditional expectations are constantly `g`,
so the identification lemma recovers `g =ᵐ μ[g | m0]`. -/
example [IsFiniteMeasure μ] {g : Ω → ℝ} (hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ) :
    g =ᵐ[μ] μ[g | ⨅ _n : ℕ, m0] :=
  MathlibExt.Probability.CondExpAntitoneLimit.condExp_antitone_limit_eq g
    (fun _ => m0) (fun _ => le_rfl) hg_int g
    (Filter.Eventually.of_forall fun ω => by
      simp only [condExp_of_stronglyMeasurable le_rfl hg_meas hg_int]
      exact tendsto_const_nhds)
    hg_int (by rw [iInf_const]; exact hg_meas)

/-- Bottom filtration: every conditional expectation is the constant `∫ g`,
and the intersection is `⊥`, so the identification lemma says the constant
function is a.e. equal to `μ[g | ⊥]`. -/
example [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg_int : Integrable g μ) :
    (fun _ : Ω => ∫ x, g x ∂μ) =ᵐ[μ] μ[g | ⨅ _n : ℕ, (⊥ : MeasurableSpace Ω)] :=
  MathlibExt.Probability.CondExpAntitoneLimit.condExp_antitone_limit_eq g
    (fun _ => ⊥) (fun _ => bot_le) hg_int (fun _ => ∫ x, g x ∂μ)
    (Filter.Eventually.of_forall fun ω => by
      simp only [condExp_bot]
      exact tendsto_const_nhds)
    (integrable_const _) (by rw [iInf_const]; exact stronglyMeasurable_const)

/-- Bottom filtration, `L¹` form: the `L¹` distance from the constant
conditional expectations to the constant `∫ g` tends to `0`. -/
example [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg_int : Integrable g μ) :
    Tendsto
      (fun _n : ℕ => eLpNorm ((μ[g | (⊥ : MeasurableSpace Ω)]) - fun _ => ∫ x, g x ∂μ) 1 μ)
      atTop (𝓝 0) :=
  MathlibExt.Probability.CondExpAntitoneLimit.tendsto_eLpNorm_condExp_sub_of_ae_tendsto
    g (fun _ => ⊥) (fun _ => bot_le)
    hg_int (fun _ => ∫ x, g x ∂μ)
    (Filter.Eventually.of_forall fun ω => by
      simp only [condExp_bot]
      exact tendsto_const_nhds)
    (integrable_const _)

end MathlibExtTest.Probability.CondExpAntitoneLimit
