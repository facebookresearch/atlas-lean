/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
public import MathlibExt.AlgebraicTopology.SimplicialCategory.TensorCotensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-! # Literal raw Reedy boundary and horn families

The outer variable is the original discrete embedding. The inner variable
is the simplicial-set boundary or positive-dimensional horn. Native chosen
pushouts retain both original injections and their strict equations.

The indices and native morphism properties are literal small families.
Their lifting and small-object properties are the subject of later results.

Source: Rezk, A model for the homotopy theory of homotopy theory (2001), §2.4.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SimplicialSpace.ReedyGeneratingFamilies

/-- Every pair of nonnegative outer and inner boundary dimensions. -/
abbrev BoundaryIndex := ℕ × ℕ

/-- An outer dimension, a positive inner dimension, and every horn face. -/
abbrev HornIndex := ℕ × (Σ n : {n : ℕ // 1 ≤ n}, Fin (n.1 + 1))

/-- The original outer boundary, made discrete innerly and designated. -/
abbrev outerBoundaryMap (m : ℕ) :
    ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (SSet.boundary.{u} m : SSet.{u})) ⟶
      ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[m] : SSet.{u})) :=
  ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map (SSet.boundary.{u} m).ι)

/-- The actual chosen inner boundary pushout, retaining both legs and their equations. -/
def boundaryPushout (m n : ℕ) :
    innerTensorBifunctor.PushoutObjObj (outerBoundaryMap.{u} m) (SSet.boundary.{u} n).ι :=
  Functor.PushoutObjObj.ofHasPushout innerTensorBifunctor
    (outerBoundaryMap.{u} m) (SSet.boundary.{u} n).ι

/-- The actual chosen inner horn pushout in every positive dimension and at every face. -/
def hornPushout (m : ℕ) (n : {n : ℕ // 1 ≤ n}) (i : Fin (n.1 + 1)) :
    innerTensorBifunctor.PushoutObjObj (outerBoundaryMap.{u} m) (SSet.horn.{u} n.1 i).ι :=
  Functor.PushoutObjObj.ofHasPushout innerTensorBifunctor
    (outerBoundaryMap.{u} m) (SSet.horn.{u} n.1 i).ι

/-- The literal indexed boundary arrows, including both zero dimensions. -/
def boundaryFamily (b : BoundaryIndex) : Arrow SimplicialSpace.{u} :=
  Arrow.mk (boundaryPushout.{u} b.1 b.2).ι

/-- The literal indexed horn arrows; no face or outer dimension is omitted. -/
def hornFamily (h : HornIndex) : Arrow SimplicialSpace.{u} :=
  Arrow.mk (hornPushout.{u} h.1 h.2.1 h.2.2).ι

/-- The literal raw Reedy boundary family as a native morphism property. -/
def I : MorphismProperty SimplicialSpace.{u} :=
  MorphismProperty.ofHoms (fun b : BoundaryIndex => (boundaryFamily.{u} b).hom)

/-- The literal raw Reedy horn family as a native morphism property. -/
def J : MorphismProperty SimplicialSpace.{u} :=
  MorphismProperty.ofHoms (fun h : HornIndex => (hornFamily.{u} h).hom)

/-- Smallness of the literal boundary family comes from its original small index. -/
lemma isSmall_I : MorphismProperty.IsSmall.{u} I.{u} :=
  MorphismProperty.isSmall_ofHoms.{u} (fun b : BoundaryIndex => (boundaryFamily.{u} b).hom)

/-- Smallness of the literal horn family comes from its original small index. -/
lemma isSmall_J : MorphismProperty.IsSmall.{u} J.{u} :=
  MorphismProperty.isSmall_ofHoms.{u} (fun h : HornIndex => (hornFamily.{u} h).hom)

end SimplicialSpace.ReedyGeneratingFamilies
