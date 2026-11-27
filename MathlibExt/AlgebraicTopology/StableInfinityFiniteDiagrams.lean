/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.Order.Category.Preord

/-!
# Actual finite cones and universal squares in an infinity category

Cone and cocone categories are the native fibres of restriction from
functors on a category with an adjoined initial or terminal object.
Universal cones use the actual mapping-space terminal/initial test.
A square is universal precisely when its particular coherent cone is
universal. Neither colimits nor square predicates are free input maps.

The four-corner index below is the literal walking commuting square,
with its coordinate order in [1] times [1]. Every shape inclusion and
extension is fixed by these coordinates.

References: Lurie, Higher Topos Theory, Section 1.2.13;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Definitions 7.1 and 7.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open scoped Simplicial

universe u

/-- Native value-universe lift of an actual small index nerve. -/
abbrev indexNerve (J : Type) [Category.{0} J] : SSet.{u} :=
  (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).obj (nerve J)

/-- The actual index functor induces its native lifted nerve map. -/
def indexMap {J K : Type} [Category.{0} J] [Category.{0} K] (F : J ⥤ K) :
    indexNerve.{u} J ⟶ indexNerve.{u} K := (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).map (nerveMap F)

/-- The lifted nerve map preserves native index identities. -/
@[simp]
theorem indexMap_id (J : Type) [Category.{0} J] : indexMap.{u} (𝟭 J) = 𝟙 (indexNerve J) := by
  ext n x
  rfl

/-- The lifted nerve map preserves the entire native index composition. -/
@[simp]
theorem indexMap_comp {J K L : Type} [Category.{0} J] [Category.{0} K] [Category.{0} L]
    (F : J ⥤ K) (G : K ⥤ L) : indexMap.{u} (F ⋙ G) = indexMap F ≫ indexMap G := by
  ext n x
  rfl

/-- Native enriched Hom restriction evaluates to ordinary precomposition at zero simplices. -/
theorem mappingZero_precomposition {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (precomposition f Z).app (op ⦋0⦌) (mappingZero Y Z g) =
      mappingZero X Z (f ≫ g) := by
  rfl

/-- The actual zero-simplex point of a native functor object. -/
def diagramPoint {J : Type} [Category.{0} J] (C : SSet.{u}) (d : indexNerve J ⟶ C) :
    Δ[0] ⟶ mapping (indexNerve J) C := SSet.const (mappingZero (indexNerve J) C d)

/-- The native category of coherent left cones on the specified diagram. -/
def leftCones {J : Type} [Category.{0} J] (C : SSet.{u}) (d : indexNerve J ⟶ C) : SSet.{u} :=
  pullback (precomposition (indexMap (WithInitial.incl (C := J))) C) (diagramPoint C d)

/-- The native category of coherent right cocones on the specified diagram. -/
def rightCones {J : Type} [Category.{0} J] (C : SSet.{u}) (d : indexNerve J ⟶ C) : SSet.{u} :=
  pullback (precomposition (indexMap (WithTerminal.incl (C := J))) C) (diagramPoint C d)

/-- A finite square has these four actual vertices. -/
inductive SquareCorner
  | origin | horizontal | vertical | final
  deriving DecidableEq

instance : Fintype SquareCorner where
  elems := { .origin, .horizontal, .vertical, .final }
  complete p := by cases p <;> simp

/-- Coordinates identify the square index with the coordinate order in [1] times [1]. -/
def SquareCorner.coordinate (p : SquareCorner) : Fin 2 × Fin 2 :=
  match p with
  | .origin => (0, 0)
  | .horizontal => (1, 0)
  | .vertical => (0, 1)
  | .final => (1, 1)

instance : PartialOrder SquareCorner where
  le a b := a.coordinate ≤ b.coordinate
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm a b hab hba := by
    have h := le_antisymm hab hba
    cases a <;> cases b <;> simp_all [SquareCorner.coordinate]

/-- The upper punctured square is the actual cospan index. -/
abbrev CospanCorner := {p : SquareCorner // p ≠ .origin}

/-- The lower punctured square is the actual span index. -/
abbrev SpanCorner := {p : SquareCorner // p ≠ .final}

/-- Include the actual cospan vertices and all their unique order arrows. -/
def cospanInclusion : CospanCorner ⥤ SquareCorner :=
  (show Monotone (fun p : CospanCorner => p.val) from fun _ _ h => h).functor

/-- Include the actual span vertices and all their unique order arrows. -/
def spanInclusion : SpanCorner ⥤ SquareCorner :=
  (show Monotone (fun p : SpanCorner => p.val) from fun _ _ h => h).functor

/-- The universal source of left cones is mapped to the original square coordinates. -/
def pullbackSquareShape : WithInitial CospanCorner ⥤ SquareCorner :=
  WithInitial.lift (Z := SquareCorner.origin) cospanInclusion
    (fun p => homOfLE (by
      change (0 : Fin 2) ≤ p.val.coordinate.1 ∧ (0 : Fin 2) ≤ p.val.coordinate.2
      exact ⟨Fin.zero_le _, Fin.zero_le _⟩)) (by
      intro x y f
      apply Subsingleton.elim)

/-- The universal source of right cocones is mapped to the original square coordinates. -/
def pushoutSquareShape : WithTerminal SpanCorner ⥤ SquareCorner :=
  WithTerminal.lift (Z := SquareCorner.final) spanInclusion
    (fun p => homOfLE (by
      change p.val.coordinate.1 ≤ (1 : Fin 2) ∧ p.val.coordinate.2 ≤ (1 : Fin 2)
      exact ⟨Fin.le_last _, Fin.le_last _⟩)) (by
      intro x y f
      apply Subsingleton.elim)

/-- A coherent square determines its actual cospan restriction. -/
def squareCospan {C : SSet.{u}} (d : indexNerve SquareCorner ⟶ C) : indexNerve CospanCorner ⟶ C :=
  indexMap cospanInclusion ≫ d

/-- A coherent square determines its actual span restriction. -/
def squareSpan {C : SSet.{u}} (d : indexNerve SquareCorner ⟶ C) : indexNerve SpanCorner ⟶ C :=
  indexMap spanInclusion ≫ d

/-- Pullback means the actual square cone is terminal among all coherent cones. -/
def IsPullbackSquare {C : SSet.{u}} (d : indexNerve SquareCorner ⟶ C) : Prop :=
  ∃ c : (leftCones C (squareCospan d)) _⦋0⦌,
    (pullback.fst (precomposition (indexMap (WithInitial.incl (C := CospanCorner))) C)
      (diagramPoint C (squareCospan d))).app (op ⦋0⦌) c =
      mappingZero (indexNerve (WithInitial CospanCorner)) C (indexMap pullbackSquareShape ≫ d) ∧
    IsTerminalObject (leftCones C (squareCospan d)) c

/-- Pushout means the actual square cocone is initial among all coherent cocones. -/
def IsPushoutSquare {C : SSet.{u}} (d : indexNerve SquareCorner ⟶ C) : Prop :=
  ∃ c : (rightCones C (squareSpan d)) _⦋0⦌,
    (pullback.fst (precomposition (indexMap (WithTerminal.incl (C := SpanCorner))) C)
      (diagramPoint C (squareSpan d))).app (op ⦋0⦌) c =
      mappingZero (indexNerve (WithTerminal SpanCorner)) C (indexMap pushoutSquareShape ≫ d) ∧
    IsInitialObject (rightCones C (squareSpan d)) c

/-- The actual value of the coherent square on a named source corner. -/
def cornerValue {C : SSet.{u}} (d : indexNerve SquareCorner ⟶ C) (p : SquareCorner) : C _⦋0⦌ :=
  d.app (op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ p))

end MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams
