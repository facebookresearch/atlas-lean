/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-! # Colimits preserved by the contravariant inner mapping functor

The genuine inner tensor/cotensor and parametrized tensor–Hom adjunctions
show that the original inner restrictions, viewed in opposite simplicial
sets, preserve every supplied colimit. Diagram objects, diagram morphisms
and simplicial values have independent universes. No existence of colimits
of arbitrary sizes or model structure is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace

/-- Inner restriction, viewed covariantly in opposite simplicial sets, preserves
each supplied colimit of any shape, with independent diagram universes. -/
theorem innerHom_rightOp_preservesColimitsOfShape
    (D : Type w) [Category.{v} D] (Z : SimplicialSpace.{u}) :
    PreservesColimitsOfShape D (innerHomFunctor.{u}.flip.obj Z).rightOp := by
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape Dᵒᵖᵒᵖ
      (innerTensorBifunctor.{u}.flip.obj K) := fun K => by
    change PreservesColimitsOfShape Dᵒᵖᵒᵖ (innerTensor K)
    let _ : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  let _ : PreservesLimitsOfShape Dᵒᵖ (innerHomFunctor.{u}.flip.obj Z) :=
    innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj Dᵒᵖ Z
  exact preservesColimitsOfShape_rightOp D (innerHomFunctor.{u}.flip.obj Z)

end SimplicialSpace
