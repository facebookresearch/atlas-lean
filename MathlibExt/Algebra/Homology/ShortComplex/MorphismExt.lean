/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# A short-complex morphism determined by its middle component

The first component is determined when the target first arrow is mono.
The last component is determined when the source last arrow is epi.
Neither exactness nor an additive structure is needed.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C}

/-- Under the two cancellation hypotheses, the middle component determines the morphism. -/
lemma hom_ext_of_mono_f_of_epi_g [Mono T.f] [Epi S.g]
    {φ ψ : S ⟶ T} (h₂ : φ.τ₂ = ψ.τ₂) : φ = ψ := by
  apply hom_ext φ ψ
  · apply (cancel_mono T.f).1
    exact φ.comm₁₂.trans
      ((congrArg (fun t => S.f ≫ t) h₂).trans ψ.comm₁₂.symm)
  · exact h₂
  · apply (cancel_epi S.g).1
    exact φ.comm₂₃.symm.trans
      ((congrArg (fun t => t ≫ T.g) h₂).trans ψ.comm₂₃)

end CategoryTheory.ShortComplex
