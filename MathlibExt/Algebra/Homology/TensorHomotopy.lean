/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal

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

/-- Tensoring two homotopies gives a homotopy between the tensor product maps. -/
noncomputable def tensorHomotopy (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (tensorHom f g) (tensorHom f' g') :=
  (mapBifunctorMapHomotopy₁ hf g (curriedTensor C) c).trans
    (mapBifunctorMapHomotopy₂ f' hg (curriedTensor C) c)

end HomologicalComplex
