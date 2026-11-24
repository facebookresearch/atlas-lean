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
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Continuous functionals on the actual ultraweak view

The proved weak representation theorem identifies every ultraweak-continuous
linear functional with evaluation against an element of the original normal
functional space. This membership certificate permits literal functional
pullback along normal maps to land in the actual predual subtype.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ultraweak continuity certifies membership in the actual closed normal-functional space. -/
theorem mem_normalFunctionalSpace_of_ultraweak_continuous (M : VonNeumannAlgebra H)
    (ψ : StrongDual ℂ M)
    (hψ : Continuous fun x : Ultraweak M => ψ (ultraweakLinearEquiv M x)) :
    ψ ∈ normalFunctionalSpace M := by
  let F : StrongDual ℂ (Ultraweak M) :=
    { toLinearMap := ψ.toLinearMap.comp (ultraweakLinearEquiv M).toLinearMap
      cont := hψ }
  obtain ⟨φ, hφ⟩ := LinearMap.dualEmbedding_surjective (normalFunctionalPairing M) F
  have hval : (φ : StrongDual ℂ M) = ψ := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg
      (fun f : StrongDual ℂ (Ultraweak M) => f ((ultraweakLinearEquiv M).symm x)) hφ
    change (φ : StrongDual ℂ M)
        (ultraweakLinearEquiv M ((ultraweakLinearEquiv M).symm x)) =
      ψ (ultraweakLinearEquiv M ((ultraweakLinearEquiv M).symm x)) at hx
    simpa only [LinearEquiv.apply_symm_apply] using hx
  exact hval ▸ φ.property

end VonNeumannAlgebra
