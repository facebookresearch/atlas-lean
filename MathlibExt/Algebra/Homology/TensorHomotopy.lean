/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Tensor products of homotopies

In a preadditive monoidal category with tensoring additive in both variables, homotopies f≃f′
and g≃g′ induce a homotopy f⊗g ≃ f′⊗g′. The construction first changes the first factor while
keeping g fixed, then changes the second while keeping f′ fixed.

The index additive monoid, tensor signs and source/target tensor existence assumptions are
retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]
variable {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
  [HasTensor K₁ K₂] [HasTensor L₁ L₂]
variable {f f' : K₁ ⟶ L₁} {g g' : K₂ ⟶ L₂}

/-- The homotopy between tensor product morphisms.

Compose the first-variable tensor homotopy of f≃f′ with the second-variable tensor homotopy of
g≃g′ to obtain f⊗g ≃ f′⊗g′. -/
noncomputable def tensorHomotopy (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (tensorHom f g) (tensorHom f' g') :=
  (mapBifunctorMapHomotopy₁ hf g (curriedTensor C) c).trans
    (mapBifunctorMapHomotopy₂ f' hg (curriedTensor C) c)

end HomologicalComplex
