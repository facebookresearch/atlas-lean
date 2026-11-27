/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatching
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Identity and degree-zero relative latching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The relative latching Arrow is the component Arrow when its latching comparison is
invertible. -/
noncomputable def relativeLatchingMapArrowIsoOfIsIso
    {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    [HasPushout (latchingMap X n) ((latchingObjectFunctor n).map f)]
    [IsIso ((latchingObjectFunctor n).map f)] :
    Arrow.mk (relativeLatchingMap f n) ≅
      Arrow.mk (f.app (op ⦋n⦌)) := by
  let i := pushout.inl (latchingMap X n)
    ((latchingObjectFunctor n).map f)
  let _ : IsIso i := inferInstance
  refine Arrow.isoMk (asIso i).symm (Iso.refl _) ?_
  apply (cancel_epi i).1
  simp [i]

/-- The relative latching arrow of an identity is isomorphic to the identity component. -/
noncomputable def relativeLatchingMapIdArrowIso
    (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    [HasPushout (latchingMap X n)
      ((latchingObjectFunctor n).map (𝟙 X))] :
    Arrow.mk (relativeLatchingMap (𝟙 X) n) ≅
      Arrow.mk (𝟙 (X.obj (op ⦋n⦌))) := by
  let _ : IsIso ((latchingObjectFunctor n).map (𝟙 X)) := inferInstance
  exact relativeLatchingMapArrowIsoOfIsIso (𝟙 X) n

/-- In degree zero, the relative latching arrow is isomorphic to the degree-zero component. -/
noncomputable def relativeLatchingMapZeroArrowIso
    [HasInitial C]
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    [HasColimitsOfShape (latchingIndex 0) C]
    [HasPushout (latchingMap X 0)
      ((latchingObjectFunctor 0).map f)] :
    Arrow.mk (relativeLatchingMap f 0) ≅
      Arrow.mk (f.app (op ⦋0⦌)) := by
  let hX : IsInitial (latchingObject X 0) :=
    initialIsInitial.ofIso (latchingObjectZeroIso X).symm
  let hY : IsInitial (latchingObject Y 0) :=
    initialIsInitial.ofIso (latchingObjectZeroIso Y).symm
  let _ : IsIso ((latchingObjectFunctor 0).map f) :=
    isIso_of_isInitial hX hY _
  exact relativeLatchingMapArrowIsoOfIsIso f 0

private noncomputable def initialSimplicialObjectObjIsInitial
    [HasInitial C] (d : SimplexCategoryᵒᵖ) :
    IsInitial ((⊥_ (SimplicialObject C)).obj d) :=
  initialIsInitial.isInitialObj
    ((evaluation SimplexCategoryᵒᵖ C).obj d) _

private noncomputable def initialLatchingCocone
    [HasInitial C] (n : ℕ)
    (Z : C) :
    Cocone (latchingDiagram (⊥_ (SimplicialObject C)) n) where
  pt := Z
  ι :=
    { app := fun a =>
        (initialSimplicialObjectObjIsInitial a.obj.left).to Z
      naturality := by
        intro a b f
        apply (initialSimplicialObjectObjIsInitial a.obj.left).hom_ext }

private noncomputable def initialLatchingObjectIsInitial
    [HasInitial C] (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    IsInitial (latchingObject (⊥_ (SimplicialObject C)) n) :=
  IsInitial.ofUniqueHom
    (fun Z => colimit.desc _ (initialLatchingCocone n Z))
    (fun _ f => by
      apply colimit.hom_ext
      intro a
      apply (initialSimplicialObjectObjIsInitial a.obj.left).hom_ext)

private theorem initialLatchingMapIsIso
    [HasInitial C] (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    IsIso (latchingMap (⊥_ (SimplicialObject C)) n) :=
  isIso_of_isInitial
    (initialLatchingObjectIsInitial n)
    (initialSimplicialObjectObjIsInitial (op ⦋n⦌)) _

/-- The relative latching arrow of the map from the initial simplicial object is canonically
isomorphic to the absolute latching arrow. -/
noncomputable def relativeLatchingMapInitialArrowIso
    [HasInitial C] [HasPushouts C] (X : SimplicialObject C) (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    Arrow.mk (relativeLatchingMap (initial.to X) n) ≅
      Arrow.mk (latchingMap X n) := by
  let _ : IsIso (latchingMap (⊥_ (SimplicialObject C)) n) := by
    exact initialLatchingMapIsIso n
  let e : Arrow.mk (latchingMap X n) ≅
      Arrow.mk (relativeLatchingMap (initial.to X) n) := by
    refine Arrow.isoMk
      (asIso (pushout.inr
        (latchingMap (⊥_ (SimplicialObject C)) n)
        ((latchingObjectFunctor n).map (initial.to X))))
      (Iso.refl _) ?_
    change pushout.inr
          (latchingMap (⊥_ (SimplicialObject C)) n)
          ((latchingObjectFunctor n).map (initial.to X)) ≫
        relativeLatchingMap (initial.to X) n =
      latchingMap X n ≫ 𝟙 _
    rw [relativeLatchingMap_inr, Category.comp_id]
  exact e.symm

end CategoryTheory.SimplicialObject
