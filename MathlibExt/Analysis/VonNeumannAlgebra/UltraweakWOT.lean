/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Original ultraweak elements map continuously to the weak operator carrier

Every original vector coefficient belongs to the actual normal-functional
space. Its ultraweak evaluation is continuous, and the stock Hilbert weak
operator topology is tested by precisely these vector coefficients. This
continuous original-value map transfers compact norm-ball images to WOT;
no norm, continuity, range or topology certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Original ultraweak algebra elements, as original operators, vary continuously in WOT. -/
theorem ultraweak_toWOT_continuous (M : VonNeumannAlgebra H) :
    Continuous (fun x : Ultraweak M =>
      ContinuousLinearMapWOT.ofCLM (ultraweakLinearEquiv M x : H →L[ℂ] H)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  have hvalue (x : Ultraweak M) :
      (normalVectorFunctional M η ξ : StrongDual ℂ M) (ultraweakLinearEquiv M x) =
        ⟪η, (ultraweakLinearEquiv M x : H →L[ℂ] H) ξ⟫_ℂ :=
    vectorFunctional_apply M η ξ (ultraweakLinearEquiv M x)
  simpa only [hvalue, ContinuousLinearMapWOT.ofCLM_apply] using
    ultraweak_eval_continuous M (normalVectorFunctional M η ξ)

end

end VonNeumannAlgebra
