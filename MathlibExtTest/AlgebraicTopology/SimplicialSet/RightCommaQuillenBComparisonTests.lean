/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenBComparison

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial unitInterval

universe u

namespace SSet

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

private abbrev selectedVertex (d : D) : SSet.toTop.obj (nerve D) :=
  SSet.realizedVertex
    (ComposableArrows.mk₀ d : (nerve D : SSet.{u}) _⦋0⦌)

private abbrev fiberAt (F : C ⥤ D) (d : D) : TopCat.{u} :=
  TopCat.homotopyFiber (SSet.toTop.map (nerveMap F)) (selectedVertex d)

private noncomputable def basepointPath {d d' : D} (g : d ⟶ d') :
    Path (selectedVertex d) (selectedVertex d') :=
  TopCat.pathEquiv
    (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g))

private noncomputable def expectedCommaPath (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      TopCat.pathObject (SSet.toTop.obj (nerve D)) :=
  TopCat.ofHom (ContinuousMap.curry
    { toFun := fun z =>
        SSet.realizeHomotopy
            (nerve (CostructuredArrow F d)) (nerve D)
            (nerveMap (CostructuredArrow.proj F d ⋙ F))
            (nerveMap ((Functor.const (CostructuredArrow F d)).obj d))
            (SSet.rightCommaArrowNerveHomotopy F d)
            (TopCat.I.homeomorph z.2, z.1)
      continuous_toFun :=
        (SSet.realizeHomotopy
            (nerve (CostructuredArrow F d)) (nerve D)
            (nerveMap (CostructuredArrow.proj F d ⋙ F))
            (nerveMap ((Functor.const (CostructuredArrow F d)).obj d))
            (SSet.rightCommaArrowNerveHomotopy F d)).continuous.comp
          ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk
            continuous_fst) })

section PublicBoundary

example (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶ fiberAt F d :=
  rightCommaHomotopyFiberComparison F d

example (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMap F)) (selectedVertex d) =
      SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) := by
  apply rightCommaHomotopyFiberComparison_toTotal

example (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMap F)) (selectedVertex d) =
      expectedCommaPath F d := by
  exact (rightCommaHomotopyFiberComparison_path.{u, 0, 0} F d).trans (by rfl)

example (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g)).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d').hom := by
  exact
    rightCommaHomotopyFiberComparison_transition_naturality_homotopy F g

end PublicBoundary

section TransitionControls

variable (F : C ⥤ D) {d d' : D} (g : d ⟶ d')

private noncomputable def transitionHomotopy :
    ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g)).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d').hom :=
  rightCommaHomotopyFiberComparison_transition_naturality_homotopy F g

example (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :
    (transitionHomotopy F g).toContinuousMap (0, z) =
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g)) z :=
  (transitionHomotopy F g).map_zero_left z

example (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :
    (transitionHomotopy F g).toContinuousMap (1, z) =
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d') z :=
  (transitionHomotopy F g).map_one_left z

/-- Postcomposition records the full compact-open path projection of the
transition homotopy, rather than merely its two path endpoints. -/
private noncomputable def transitionPathProjectionHomotopy :
    ContinuousMap.Homotopy
      ((rightCommaHomotopyFiberComparison F d ≫
          TopCat.homotopyFiberBasepointChange
            (SSet.toTop.map (nerveMap F)) (basepointPath g)) ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom
      ((SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaHomotopyFiberComparison F d') ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom := by
  let H := ContinuousMap.Homotopy.comp
    (ContinuousMap.Homotopy.refl
      (TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom)
    (transitionHomotopy F g)
  exact H.cast
    (TopCat.hom_comp
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g))
      (TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMap F)) (selectedVertex d'))).symm
    (TopCat.hom_comp
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d')
      (TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMap F)) (selectedVertex d'))).symm

example : Nonempty <|
    ContinuousMap.Homotopy
      ((rightCommaHomotopyFiberComparison F d ≫
          TopCat.homotopyFiberBasepointChange
            (SSet.toTop.map (nerveMap F)) (basepointPath g)) ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom
      ((SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaHomotopyFiberComparison F d') ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom :=
  ⟨transitionPathProjectionHomotopy F g⟩

private theorem transitionSource_toTotal :
    (rightCommaHomotopyFiberComparison F d ≫
          TopCat.homotopyFiberBasepointChange
            (SSet.toTop.map (nerveMap F)) (basepointPath g)) ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMap F)) (selectedVertex d') =
      SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) := by
  calc
    _ = rightCommaHomotopyFiberComparison F d ≫
        (TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g) ≫
          TopCat.homotopyFiberToTotal
            (SSet.toTop.map (nerveMap F)) (selectedVertex d')) :=
      Category.assoc _ _ _
    _ = rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMap F)) (selectedVertex d) :=
      congrArg
        (fun m : fiberAt F d ⟶ SSet.toTop.obj (nerve C) =>
          rightCommaHomotopyFiberComparison F d ≫ m)
        (TopCat.homotopyFiberBasepointChange_toTotal
          (SSet.toTop.map (nerveMap F)) (basepointPath g))
    _ = SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) :=
      rightCommaHomotopyFiberComparison_toTotal.{u, 0, 0} F d

private theorem transitionTarget_toTotal :
    (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaHomotopyFiberComparison F d') ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMap F)) (selectedVertex d') =
      SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) := by
  calc
    _ = SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        (rightCommaHomotopyFiberComparison F d' ≫
          TopCat.homotopyFiberToTotal
            (SSet.toTop.map (nerveMap F)) (selectedVertex d')) :=
      Category.assoc _ _ _
    _ = SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        SSet.toTop.map (nerveMap (CostructuredArrow.proj F d')) :=
      congrArg
        (fun m : SSet.toTop.obj (nerve (CostructuredArrow F d')) ⟶
            SSet.toTop.obj (nerve C) =>
          SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫ m)
        (rightCommaHomotopyFiberComparison_toTotal.{u, 0, 0} F d')
    _ = SSet.toTop.map
        (nerveMap (CostructuredArrow.map g) ≫
          nerveMap (CostructuredArrow.proj F d')) :=
      (SSet.toTop.map_comp _ _).symm
    _ = SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) :=
      congrArg SSet.toTop.map (rightCommaProjection_naturality.{u, 0, 0} F g)

/-- Both endpoints have the same total coordinate.  Postcomposition therefore
gives an explicitly typed homotopy from that projection to itself. -/
private noncomputable def transitionTotalProjectionHomotopy :
    ContinuousMap.Homotopy
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F d))).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F d))).hom := by
  let H := ContinuousMap.Homotopy.comp
    (ContinuousMap.Homotopy.refl
      (TopCat.homotopyFiberToTotal
        (SSet.toTop.map (nerveMap F)) (selectedVertex d')).hom)
    (transitionHomotopy F g)
  exact H.cast
    (congrArg TopCat.Hom.hom (transitionSource_toTotal F g))
    (congrArg TopCat.Hom.hom (transitionTarget_toTotal F g))

example : Nonempty <| ContinuousMap.Homotopy
    (SSet.toTop.map (nerveMap (CostructuredArrow.proj F d))).hom
    (SSet.toTop.map (nerveMap (CostructuredArrow.proj F d))).hom :=
  ⟨transitionTotalProjectionHomotopy F g⟩

example : Nonempty <| ContinuousMap.Homotopy
    (rightCommaHomotopyFiberComparison F d ≫
      TopCat.homotopyFiberBasepointChange
        (SSet.toTop.map (nerveMap F)) (basepointPath (𝟙 d))).hom
    (SSet.toTop.map (nerveMap (CostructuredArrow.map (𝟙 d))) ≫
      rightCommaHomotopyFiberComparison F d).hom :=
  ⟨rightCommaHomotopyFiberComparison_transition_naturality_homotopy
    F (𝟙 d)⟩

end TransitionControls

section NonidentityFixture

private def nonidentityFunctor : Fin 1 ⥤ Fin 3 :=
  (Functor.const (Fin 1)).obj (0 : Fin 3)

private def firstArrow : (0 : Fin 3) ⟶ (1 : Fin 3) :=
  homOfLE (by decide)

private def secondArrow : (1 : Fin 3) ⟶ (2 : Fin 3) :=
  homOfLE (by decide)

private def nonidentityCommaObject :
    CostructuredArrow nonidentityFunctor (1 : Fin 3) :=
  CostructuredArrow.mk (Y := (0 : Fin 1)) firstArrow

private noncomputable def nonidentityCommaPoint :
    SSet.toTop.obj
      (nerve (CostructuredArrow nonidentityFunctor (1 : Fin 3))) :=
  SSet.realizedVertex (ComposableArrows.mk₀ nonidentityCommaObject)

example : nonidentityCommaObject.hom ≫ secondArrow =
    homOfLE (show (0 : Fin 3) ≤ 2 by decide) := by
  apply Subsingleton.elim

example :
    (rightCommaHomotopyFiberComparison_transition_naturality_homotopy
        nonidentityFunctor secondArrow).toContinuousMap
        (0, nonidentityCommaPoint) =
      (rightCommaHomotopyFiberComparison nonidentityFunctor (1 : Fin 3) ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap nonidentityFunctor))
          (basepointPath secondArrow)) nonidentityCommaPoint :=
  (rightCommaHomotopyFiberComparison_transition_naturality_homotopy
    nonidentityFunctor secondArrow).map_zero_left nonidentityCommaPoint

example :
    (rightCommaHomotopyFiberComparison_transition_naturality_homotopy
        nonidentityFunctor secondArrow).toContinuousMap
        (1, nonidentityCommaPoint) =
      (SSet.toTop.map (nerveMap (CostructuredArrow.map secondArrow)) ≫
        rightCommaHomotopyFiberComparison
          nonidentityFunctor (2 : Fin 3)) nonidentityCommaPoint :=
  (rightCommaHomotopyFiberComparison_transition_naturality_homotopy
    nonidentityFunctor secondArrow).map_one_left nonidentityCommaPoint

end NonidentityFixture

section DegenerateFixtures

private def terminalFunctor : Fin 2 ⥤ Fin 1 :=
  (Functor.const (Fin 2)).obj (0 : Fin 1)

example : SSet.toTop.obj
      (nerve (CostructuredArrow terminalFunctor (0 : Fin 1))) ⟶
    fiberAt terminalFunctor (0 : Fin 1) :=
  rightCommaHomotopyFiberComparison terminalFunctor 0

example : SSet.toTop.obj
      (nerve (CostructuredArrow (Functor.id (Fin 2)) (1 : Fin 2))) ⟶
    fiberAt (Functor.id (Fin 2)) (1 : Fin 2) :=
  rightCommaHomotopyFiberComparison (Functor.id (Fin 2)) 1

private def emptyCommaFunctor : Fin 1 ⥤ Fin 2 :=
  (Functor.const (Fin 1)).obj (1 : Fin 2)

private instance : IsEmpty
    (CostructuredArrow emptyCommaFunctor (0 : Fin 2)) where
  false X := by
    have hle : (1 : Fin 2) ≤ 0 := leOfHom X.hom
    omega

example : SSet.toTop.obj
      (nerve (CostructuredArrow emptyCommaFunctor (0 : Fin 2))) ⟶
    fiberAt emptyCommaFunctor (0 : Fin 2) :=
  rightCommaHomotopyFiberComparison emptyCommaFunctor 0

example : Nonempty <| ContinuousMap.Homotopy
    (rightCommaHomotopyFiberComparison emptyCommaFunctor (0 : Fin 2) ≫
      TopCat.homotopyFiberBasepointChange
        (SSet.toTop.map (nerveMap emptyCommaFunctor))
        (basepointPath (𝟙 (0 : Fin 2)))).hom
    (SSet.toTop.map
        (nerveMap (CostructuredArrow.map (𝟙 (0 : Fin 2)))) ≫
      rightCommaHomotopyFiberComparison
        emptyCommaFunctor (0 : Fin 2)).hom :=
  ⟨rightCommaHomotopyFiberComparison_transition_naturality_homotopy
    emptyCommaFunctor (𝟙 (0 : Fin 2))⟩

end DegenerateFixtures

section UniverseControls

example {C₁ D₁ : Type 1} [Category.{0} C₁] [Category.{0} D₁]
    (F : C₁ ⥤ D₁) {d d' : D₁} (g : d ⟶ d') :
    Nonempty <| ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g)).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d').hom :=
  ⟨rightCommaHomotopyFiberComparison_transition_naturality_homotopy F g⟩

example {C₀ D₀ : Type} [Category.{0} C₀] [Category.{0} D₀]
    (F : C₀ ⥤ D₀) {d d' : D₀} (g : d ⟶ d') :
    Nonempty <| ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMap F)) (basepointPath g)).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d').hom :=
  ⟨rightCommaHomotopyFiberComparison_transition_naturality_homotopy F g⟩

end UniverseControls

/-! Representative construction helpers remain private. -/

/-- error: Unknown constant `SSet.transitionFiberFamilyMap` -/
#guard_msgs (error) in
#check SSet.transitionFiberFamilyMap

/-- error: Unknown constant `SSet.compositionPathHomotopy` -/
#guard_msgs (error) in
#check SSet.compositionPathHomotopy

/-- error: Unknown constant `SSet.rightCommaHomotopyFiberComparisonProbe` -/
#guard_msgs (error) in
#check SSet.rightCommaHomotopyFiberComparisonProbe

/-! No stronger conclusion is exported. -/

/-- error: Unknown constant `SSet.rightCommaHomotopyFiberComparison_transition_weakEquivalence` -/
#guard_msgs (error) in
#check SSet.rightCommaHomotopyFiberComparison_transition_weakEquivalence

/-- error: Unknown constant `SSet.leftCommaHomotopyFiberComparison` -/
#guard_msgs (error) in
#check SSet.leftCommaHomotopyFiberComparison

/-- error: Unknown constant `SSet.rightCommaQuillenB` -/
#guard_msgs (error) in
#check SSet.rightCommaQuillenB

#check rightCommaHomotopyFiberComparison
#check rightCommaHomotopyFiberComparison_toTotal
#check rightCommaHomotopyFiberComparison_path
#check rightCommaHomotopyFiberComparison_transition_naturality_homotopy

#print axioms rightCommaHomotopyFiberComparison
#print axioms rightCommaHomotopyFiberComparison_toTotal
#print axioms rightCommaHomotopyFiberComparison_path
#print axioms
  rightCommaHomotopyFiberComparison_transition_naturality_homotopy

end SSet

end
