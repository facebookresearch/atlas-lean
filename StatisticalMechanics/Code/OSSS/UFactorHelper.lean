/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Code.OSSS.AdaptCondBBProof2

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]















theorem ofh_factor_one_component (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ)
    {G : (Fin n → ℝ) → ℝ} (hGm : Measurable G) {CG : ℝ} (hGC : ∀ U, |G U| ≤ CG) :
    (∫ U, truncInd μ σ f U (t + 1) * G U ∂(cube n))
      = ∫ A, acp_truncHead μ σ f t A
          * (∫ B, G (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) :=
  ubf_integral_factor_of_factors n t
    (h := fun U => truncInd μ σ f U (t + 1))
    (h₀ := acp_truncHead μ σ f t)
    (fun U => acp_truncInd_factors μ σ f t U)
    (acp_measurable_truncHead μ σ f t)
    (fun A => acp_truncHead_le_one μ σ f t A)
    hGm hGC

end AdaptDisintegration

end OSSS

end StatMech
