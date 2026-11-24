/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialObject.Latching
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Owner tests for functorial simplicial latching objects
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace MathlibExtTest.SimplicialObject.LatchingTests

open CategoryTheory.SimplicialObject

-- Original latching API, in provider order.
#check SimplicialObject.latchingIndex
#check SimplicialObject.latchingDiagramFunctor
#check SimplicialObject.latchingDiagram
#check SimplicialObject.latchingDiagramFunctor_map_app
#check SimplicialObject.latchingCocone
#check SimplicialObject.latchingObjectFunctor
#check SimplicialObject.latchingObject
#check SimplicialObject.latchingι
#check SimplicialObject.latchingObjectFunctor_map_ι
#check SimplicialObject.latchingMapNatTrans
#check SimplicialObject.latchingMap
#check SimplicialObject.latchingMap_ι
#check SimplicialObject.latchingMap_naturality
#check SimplicialObject.latchingMapArrowFunctor
#check SimplicialObject.latchingMapArrowFunctor_obj
#check SimplicialObject.latchingMapArrowIso
#check SimplicialObject.latchingObjectZeroIso
#check SimplicialObject.latchingMapZeroArrowIso
#check SimplicialObject.DegeneraciesIn
#check SimplicialObject.LatchingMapsIn

#synth Finite (SimplicialObject.latchingIndex 0)
#synth Finite (SimplicialObject.latchingIndex 1)
#synth Finite (SimplicialObject.latchingIndex 7)

-- Independent category/object universe corners.
#check @SimplicialObject.latchingDiagramFunctor.{0, 0}
#check @SimplicialObject.latchingDiagramFunctor.{1, 1}
#check @SimplicialObject.latchingDiagramFunctor.{0, 1}
#check @SimplicialObject.latchingDiagramFunctor.{1, 0}
#check @SimplicialObject.latchingMapArrowFunctor.{0, 0}
#check @SimplicialObject.latchingMapArrowFunctor.{1, 1}
#check @SimplicialObject.latchingMapArrowFunctor.{0, 1}
#check @SimplicialObject.latchingMapArrowFunctor.{1, 0}

section Orientation

variable {n : ℕ} {a b : SimplicialObject.latchingIndex n}

example : SimplicialObject.latchingIndexComma n :=
  a.obj

example (f : a ⟶ b) :
    b.obj.hom.unop ≫ f.hom.left.unop = a.obj.hom.unop := by
  apply Quiver.Hom.op_inj
  simp

#guard_msgs (error, substring := true) in
example (f : a ⟶ b) :
    a.obj.hom.unop ≫ f.hom.left.unop = b.obj.hom.unop := by
  rfl

end Orientation

private def pointToBool : PUnit.{1} ⟶ Bool :=
  TypeCat.ofHom (fun _ => true)

private def boolToPoint : Bool ⟶ PUnit.{1} :=
  TypeCat.ofHom (fun _ => PUnit.unit)

private def constPoint : SimplicialObject (Type) :=
  (Functor.const SimplexCategoryᵒᵖ).obj PUnit

private def constBool : SimplicialObject (Type) :=
  (Functor.const SimplexCategoryᵒᵖ).obj Bool

private def constPointToBool : constPoint ⟶ constBool :=
  (Functor.const SimplexCategoryᵒᵖ).map pointToBool

private def constBoolToPoint : constBool ⟶ constPoint :=
  (Functor.const SimplexCategoryᵒᵖ).map boolToPoint

section Functoriality

variable {C : Type u} [Category.{v} C]
variable (n : ℕ) [HasColimitsOfShape (SimplicialObject.latchingIndex n) C]
variable {X Y Z : SimplicialObject C} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (a : SimplicialObject.latchingIndex n)

example :
    SimplicialObject.latchingDiagram X n ⟶ SimplicialObject.latchingDiagram Y n :=
  SimplicialObject.latchingDiagramMap n f

example :
    (SimplicialObject.latchingDiagramFunctor n).map f =
      SimplicialObject.latchingDiagramMap n f :=
  rfl

example :
    (SimplicialObject.latchingDiagramMap n f).app a = f.app a.obj.left :=
  rfl

example :
    ((SimplicialObject.latchingDiagramFunctor n).map f).app a =
      f.app a.obj.left :=
  SimplicialObject.latchingDiagramFunctor_map_app n f a

example :
    (SimplicialObject.latchingDiagramFunctor n).map (𝟙 X) = 𝟙 _ :=
  (SimplicialObject.latchingDiagramFunctor n).map_id X

example :
    (SimplicialObject.latchingDiagramFunctor n).map (f ≫ g) =
      (SimplicialObject.latchingDiagramFunctor n).map f ≫
        (SimplicialObject.latchingDiagramFunctor n).map g :=
  (SimplicialObject.latchingDiagramFunctor n).map_comp f g

example {a b : SimplicialObject.latchingIndex n} (h : a ⟶ b) :
    (SimplicialObject.latchingDiagram X n).map h ≫
        (SimplicialObject.latchingCocone X n).ι.app b =
      (SimplicialObject.latchingCocone X n).ι.app a :=
  (SimplicialObject.latchingCocone X n).w h

example :
    SimplicialObject.latchingι X n a ≫
        (SimplicialObject.latchingObjectFunctor n).map f =
      f.app a.obj.left ≫ SimplicialObject.latchingι Y n a :=
  SimplicialObject.latchingObjectFunctor_map_ι n f a

example :
    (SimplicialObject.latchingObjectFunctor n).map (𝟙 X) = 𝟙 _ :=
  (SimplicialObject.latchingObjectFunctor n).map_id X

example :
    (SimplicialObject.latchingObjectFunctor n).map (f ≫ g) =
      (SimplicialObject.latchingObjectFunctor n).map f ≫
        (SimplicialObject.latchingObjectFunctor n).map g :=
  (SimplicialObject.latchingObjectFunctor n).map_comp f g

example :
    (SimplicialObject.latchingMapNatTrans n).app X =
      SimplicialObject.latchingMap X n :=
  rfl

example :
    SimplicialObject.latchingι X n a ≫
        SimplicialObject.latchingMap X n = X.map a.obj.hom :=
  SimplicialObject.latchingMap_ι X n a

example :
    (SimplicialObject.latchingObjectFunctor n).map f ≫
        SimplicialObject.latchingMap Y n =
      SimplicialObject.latchingMap X n ≫ f.app (op ⦋n⦌) :=
  SimplicialObject.latchingMap_naturality n f

example :
    ((SimplicialObject.latchingMapArrowFunctor n).map f).left =
      (SimplicialObject.latchingObjectFunctor n).map f :=
  rfl

example :
    ((SimplicialObject.latchingMapArrowFunctor n).map f).right =
      f.app (op ⦋n⦌) :=
  rfl

example :
    ((SimplicialObject.latchingMapArrowFunctor n).map f).left ≫
        SimplicialObject.latchingMap Y n =
      SimplicialObject.latchingMap X n ≫
        ((SimplicialObject.latchingMapArrowFunctor n).map f).right :=
  Arrow.w ((SimplicialObject.latchingMapArrowFunctor n).map f)

example :
    (SimplicialObject.latchingMapArrowFunctor n).map (𝟙 X) = 𝟙 _ :=
  (SimplicialObject.latchingMapArrowFunctor n).map_id X

example :
    (SimplicialObject.latchingMapArrowFunctor n).map (f ≫ g) =
      (SimplicialObject.latchingMapArrowFunctor n).map f ≫
        (SimplicialObject.latchingMapArrowFunctor n).map g :=
  (SimplicialObject.latchingMapArrowFunctor n).map_comp f g

example (e : X ≅ Y) :
    SimplicialObject.latchingMapArrowIso n e =
      (SimplicialObject.latchingMapArrowFunctor n).mapIso e :=
  rfl

end Functoriality

section ConcreteNonidentity

variable (n : ℕ)

example (a : SimplicialObject.latchingIndex n) :
    ((SimplicialObject.latchingDiagramFunctor n).map
      constPointToBool).app a = pointToBool :=
  rfl

example :
    (SimplicialObject.latchingMapArrowFunctor n).map
        (constPointToBool ≫ constBoolToPoint) =
      (SimplicialObject.latchingMapArrowFunctor n).map constPointToBool ≫
        (SimplicialObject.latchingMapArrowFunctor n).map
          constBoolToPoint :=
  (SimplicialObject.latchingMapArrowFunctor n).map_comp _ _

end ConcreteNonidentity

private theorem degreeZeroIsEmpty :
    IsEmpty (SimplicialObject.latchingIndex 0) :=
  ⟨fun a => (Nat.not_lt_zero _ a.property.2).elim⟩

section DegreeZero

variable {C : Type u} [Category.{v} C] [HasInitial C]
variable [HasColimitsOfShape (SimplicialObject.latchingIndex 0) C]
variable (X : SimplicialObject C)

example : SimplicialObject.latchingObject X 0 ≅ ⊥_ C :=
  SimplicialObject.latchingObjectZeroIso X

example :
    (SimplicialObject.latchingMapArrowFunctor 0).obj X ≅
      Arrow.mk (initial.to (X.obj (op ⦋0⦌))) :=
  SimplicialObject.latchingMapZeroArrowIso X

example :
    (SimplicialObject.latchingMapZeroArrowIso X).hom.left =
      (SimplicialObject.latchingObjectZeroIso X).hom :=
  rfl

example :
    (SimplicialObject.latchingMapZeroArrowIso X).hom.right = 𝟙 _ :=
  rfl

end DegreeZero

private def degreeOneIndex : SimplicialObject.latchingIndex 1 :=
  ⟨CostructuredArrow.mk
      (SimplexCategory.σ (0 : Fin 1)).op,
    ⟨by
      change Epi (SimplexCategory.σ (0 : Fin 1))
      infer_instance,
      by simp⟩⟩

section DegreeOneAndCircle

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape (SimplicialObject.latchingIndex 1) C]

example (X : SimplicialObject C) :
    SimplicialObject.latchingι X 1 degreeOneIndex ≫
        SimplicialObject.latchingMap X 1 = X.σ 0 := by
  simpa [degreeOneIndex, SimplicialObject.σ_def] using
    SimplicialObject.latchingMap_ι X 1 degreeOneIndex

example :
    SimplicialObject.latchingι SSet.S1 1 degreeOneIndex ≫
        SimplicialObject.latchingMap SSet.S1 1 = SSet.S1.σ 0 := by
  simpa [degreeOneIndex, SimplicialObject.σ_def] using
    SimplicialObject.latchingMap_ι SSet.S1 1 degreeOneIndex

end DegreeOneAndCircle

section Predicates

example : constPoint.DegeneraciesIn
    (MorphismProperty.isomorphisms (Type)) := by
  intro n i
  change IsIso (𝟙 PUnit)
  infer_instance

example : constPoint.LatchingMapsIn (⊤ : MorphismProperty (Type)) := by
  intro n
  trivial

end Predicates

-- Auxiliary proofs and finite-index encodings remain private.
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingIndexHomEquiv
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingIndexFiniteData
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingDiagramMap_id
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingDiagramMap_comp
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingCocone_w
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingObjectFunctor_map_desc
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingMapNatTrans_w
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingMapArrowFunctor_map
#guard_msgs (error, substring := true) in
#check SimplicialObject.latchingIndexZero_isEmpty

-- Rejected aliases and stronger structures.
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeLatchingMap
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingObject
#guard_msgs (error, substring := true) in
#check SimplicialObject.ReedyCofibrant
#guard_msgs (error, substring := true) in
#check SimplicialObject.instReedyModelCategory
#guard_msgs (error, substring := true) in
#check CGWH.Simplicial.latchingObject

#print axioms SimplicialObject.latchingIndex
#print axioms SimplicialObject.latchingDiagramFunctor
#print axioms SimplicialObject.latchingDiagram
#print axioms SimplicialObject.latchingDiagramFunctor_map_app
#print axioms SimplicialObject.latchingCocone
#print axioms SimplicialObject.latchingObjectFunctor
#print axioms SimplicialObject.latchingObject
#print axioms SimplicialObject.latchingι
#print axioms SimplicialObject.latchingObjectFunctor_map_ι
#print axioms SimplicialObject.latchingMapNatTrans
#print axioms SimplicialObject.latchingMap
#print axioms SimplicialObject.latchingMap_ι
#print axioms SimplicialObject.latchingMap_naturality
#print axioms SimplicialObject.latchingMapArrowFunctor
#print axioms SimplicialObject.latchingMapArrowFunctor_obj
#print axioms SimplicialObject.latchingMapArrowIso
#print axioms SimplicialObject.latchingObjectZeroIso
#print axioms SimplicialObject.latchingMapZeroArrowIso
#print axioms SimplicialObject.DegeneraciesIn
#print axioms SimplicialObject.LatchingMapsIn

end MathlibExtTest.SimplicialObject.LatchingTests
