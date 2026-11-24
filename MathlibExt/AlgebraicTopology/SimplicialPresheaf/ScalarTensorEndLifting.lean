/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Original scalar tensor and end lifting

The actual scalar tensor/end adjunction is parametrized by the original
presheaf. The native heterogeneous Arrow-square and lift equivalences can
therefore be applied directly to every supplied tensor pushout and mapping
pullback. All original presheaf maps remain in their declared Hom universes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The actual tensor/end adjunction, parametrized by the original source presheaf. -/
def scalarTensorHomAdjunction₂ :
    scalarTensor (D := D) ⊣₂ innerHomFunctor (D := D) :=
  ParametrizedAdjunction.mk' scalarTensorHomAdjunction (by
    intro A B a K Z f
    rw [scalarTensorHomAdjunction_homEquiv, scalarTensorHomAdjunction_homEquiv]
    exact scalarTensorHomEquiv_source a K Z f)

/-- Each component is the same previously constructed scalar adjunction. -/
theorem scalarTensorHomAdjunction₂_adj (A : SimplicialPresheaf.{u} D) :
    (scalarTensorHomAdjunction₂ (D := D)).adj A = scalarTensorHomAdjunction A := rfl

/-- Native parametrized transposition is the original scalar end transposition. -/
theorem scalarTensorHomAdjunction₂_homEquiv (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) :
    (scalarTensorHomAdjunction₂ (D := D)).homEquiv
      (X₁ := A) (X₂ := K) (X₃ := Z) = scalarTensorHomEquiv A K Z := by
  change (scalarTensorHomAdjunction A).homEquiv K Z = _
  rw [scalarTensorHomAdjunction_homEquiv]

end SimplicialPresheaf
