/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Matching

/-!
# Tests for functorial matching objects
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.SimplicialObjectMatching

variable {C : Type u} [Category.{v} C]

example (n : ℕ) : Finite (SimplicialObject.matchingIndex n) := inferInstance

private noncomputable def matchingVertex (i : Fin 2) :
    SimplicialObject.matchingIndex 1 :=
  ⟨StructuredArrow.mk (SimplexCategory.δ i).op, by
    constructor
    · change Mono (SimplexCategory.δ i)
      infer_instance
    · simp⟩

example (i : Fin 2) : (matchingVertex i).obj.hom.unop = SimplexCategory.δ i :=
  rfl

example (i : Fin 2) : (matchingVertex i).obj.right.unop.len = 0 :=
  rfl

section Matching

variable [∀ n : ℕ, HasLimitsOfShape (SimplicialObject.matchingIndex n) C]
variable (X : SimplicialObject C) (n : ℕ)

example : SimplicialObject C ⥤
    (SimplicialObject.matchingIndex n ⥤ C) :=
  SimplicialObject.matchingDiagramFunctor n

example : (SimplicialObject.matchingDiagramFunctor (C := C) n).map (𝟙 X) = 𝟙 _ := by
  simp

example {Y Z : SimplicialObject C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (SimplicialObject.matchingDiagramFunctor (C := C) n).map (f ≫ g) =
      (SimplicialObject.matchingDiagramFunctor n).map f ≫
        (SimplicialObject.matchingDiagramFunctor n).map g := by
  simp

example : SimplicialObject C ⥤ C :=
  SimplicialObject.matchingObjectFunctor n

example : X.obj (op ⦋n⦌) ⟶ SimplicialObject.matchingObject X n :=
  SimplicialObject.matchingMap X n

example (a : SimplicialObject.matchingIndex n) :
    SimplicialObject.matchingObject X n ⟶ X.obj a.obj.right :=
  SimplicialObject.matchingπ X n a

example {Y : SimplicialObject C} (f : X ⟶ Y)
    (a : SimplicialObject.matchingIndex n) :
    (SimplicialObject.matchingObjectFunctor n).map f ≫
        SimplicialObject.matchingπ Y n a =
      SimplicialObject.matchingπ X n a ≫ f.app a.obj.right :=
  SimplicialObject.matchingObjectFunctor_map_π n f a

example (a : SimplicialObject.matchingIndex n) :
    SimplicialObject.matchingMap X n ≫
        SimplicialObject.matchingπ X n a = X.map a.obj.hom :=
  SimplicialObject.matchingMap_π X n a

example (i : Fin 2) :
    SimplicialObject.matchingMap X 1 ≫
        SimplicialObject.matchingπ X 1 (matchingVertex i) =
      X.map (SimplexCategory.δ i).op := by
  simpa [matchingVertex] using
    SimplicialObject.matchingMap_π X 1 (matchingVertex i)

example {Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ SimplicialObject.matchingMap Y n =
      SimplicialObject.matchingMap X n ≫
        (SimplicialObject.matchingObjectFunctor n).map f :=
  SimplicialObject.matchingMap_naturality n f

example : SimplicialObject C ⥤ Arrow C :=
  SimplicialObject.matchingMapArrowFunctor n

example {Y : SimplicialObject C} (f : X ⟶ Y) :
    ((SimplicialObject.matchingMapArrowFunctor n).map f).left =
      f.app (op ⦋n⦌) :=
  rfl

example {Y : SimplicialObject C} (f : X ⟶ Y) :
    ((SimplicialObject.matchingMapArrowFunctor n).map f).right =
      (SimplicialObject.matchingObjectFunctor n).map f :=
  rfl

example {Y : SimplicialObject C} (f : X ⟶ Y) :
    ((SimplicialObject.matchingMapArrowFunctor n).map f).left ≫
        SimplicialObject.matchingMap Y n =
      SimplicialObject.matchingMap X n ≫
        ((SimplicialObject.matchingMapArrowFunctor n).map f).right :=
  Arrow.w ((SimplicialObject.matchingMapArrowFunctor n).map f)

example {Y : SimplicialObject C} (e : X ≅ Y) :
    Arrow.mk (SimplicialObject.matchingMap X n) ≅
      Arrow.mk (SimplicialObject.matchingMap Y n) :=
  SimplicialObject.matchingMapArrowIso n e

end Matching

section Zero

variable [HasTerminal C]
variable [HasLimitsOfShape (SimplicialObject.matchingIndex 0) C]
variable (X : SimplicialObject C)

example : SimplicialObject.matchingObject X 0 ≅ ⊤_ C :=
  SimplicialObject.matchingObjectZeroIso X

example :
    (SimplicialObject.matchingMapArrowFunctor 0).obj X ≅
      Arrow.mk (terminal.from (X.obj (op ⦋0⦌))) :=
  SimplicialObject.matchingMapZeroArrowIso X

end Zero

section UniverseMatrix

#check SimplicialObject.matchingDiagramFunctor (C := Type) 0
#check SimplicialObject.matchingObjectFunctor (C := Type) 0
#check SimplicialObject.matchingMapNatTrans (C := Type) 0

#check SimplicialObject.matchingDiagramFunctor (C := Type 1) 1
#check SimplicialObject.matchingObjectFunctor (C := Type 1) 1
#check SimplicialObject.matchingMapNatTrans (C := Type 1) 1

end UniverseMatrix

-- Provider implementation helpers remain hidden.
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingIndexBound
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingIndexExtend
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingIndexEncode
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingIndexEncode_apply
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingIndexEncode_injective
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingMapApp
#guard_msgs (error, substring := true) in
#check SimplicialObject.matchingMapApp_π

-- Rejected orientations and stronger structures.
#guard_msgs (error, substring := true) in
#synth Mono (SimplexCategory.σ (n := 0) 0)
#guard_msgs (error, substring := true) in
#check SimplicialObject.relativeMatchingMap
#guard_msgs (error, substring := true) in
#check SimplicialObject.ReedyFibrant
#guard_msgs (error, substring := true) in
#check SimplicialObject.reedyModelCategory

#print axioms SimplicialObject.matchingDiagramFunctor
#print axioms SimplicialObject.matchingCone
#print axioms SimplicialObject.matchingObjectFunctor
#print axioms SimplicialObject.matchingπ
#print axioms SimplicialObject.matchingObjectFunctor_map_π
#print axioms SimplicialObject.matchingMapNatTrans
#print axioms SimplicialObject.matchingMap_π
#print axioms SimplicialObject.matchingMap_naturality
#print axioms SimplicialObject.matchingMapArrowFunctor
#print axioms SimplicialObject.matchingMapArrowIso
#print axioms SimplicialObject.matchingObjectZeroIso
#print axioms SimplicialObject.matchingMapZeroArrowIso

end MathlibExtTest.SimplicialObjectMatching
