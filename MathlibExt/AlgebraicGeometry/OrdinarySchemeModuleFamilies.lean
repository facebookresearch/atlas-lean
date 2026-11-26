/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
public import Mathlib.Algebra.Category.AlgCat.Basic

/-!
# Actual ordinary affine families and full categorical Perf

Every family is an actual commutative ring and scheme map Spec(R)→X.
The canonical integer algebra structure permits all commutative rings.
The coefficient simplicial algebra is literally constant R. The full
QCoh category is native cocartesian sections over all these ordinary
affine families. Perfectness uses the original finite-cell/retract
DG-module test in every actual affine coefficient fibre.

Pullback is native section reindexing by the original scheme map.
This ordinary source does not use a pi0-only derived prestack as a
replacement for the classical scheme.

Sources: Bhatt--Mathew1807.04725v4, Notation5.8/Theorem5.16;
Lurie, Higher Algebra, Section7.3; native affine DG scalar/source
constructions retain their pinned source attribution in the imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open GeneralArcCoverModels SimplicialAlgebraGeometry DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

/-- The canonical integer algebra source includes every actual commutative ring. -/
abbrev OrdinaryAlgebras := CommAlgCat.{0} ℤ

abbrev ordinaryRings : OrdinaryAlgebras ⥤ CommRingCat.{0} :=
  forget₂ OrdinaryAlgebras CommRingCat

/-- Each original coefficient ring is the literal constant simplicial algebra. -/
def constantCoefficients : OrdinaryAlgebras ⥤ SAlg ℤ :=
  _root_.CategoryTheory.Functor.const SimplexCategoryᵒᵖ

/-- An ordinary affine family is the actual Spec test on the original scheme. -/
structure Family (X : QcqsScheme) where
  algebra : OrdinaryAlgebras
  map : Spec (ordinaryRings.obj algebra) ⟶ X.scheme

/-- Every family map is the original algebra map with its literal Spec test square. -/
structure FamilyHom {X : QcqsScheme} (A B : Family X) where
  algebra : A.algebra ⟶ B.algebra
  square : Spec.map (ordinaryRings.map algebra) ≫ A.map = B.map

@[ext]
theorem FamilyHom.ext {X : QcqsScheme} {A B : Family X} (f g : FamilyHom A B)
    (h : f.algebra = g.algebra) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance familyCategory (X : QcqsScheme) : Category.{0} (Family X) where
  Hom := FamilyHom
  id A := ⟨𝟙 A.algebra, by simp⟩
  comp f g := ⟨f.algebra ≫ g.algebra, by
    rw [_root_.CategoryTheory.Functor.map_comp, Spec.map_comp, Category.assoc, f.square, g.square]⟩
  id_comp f := by apply FamilyHom.ext; simp
  comp_id f := by apply FamilyHom.ext; simp
  assoc f g h := by apply FamilyHom.ext; simp

/-- The actual original ring projection of the full ordinary affine family category. -/
def ringProjection (X : QcqsScheme) : Family X ⥤ OrdinaryAlgebras where
  obj a := a.algebra
  map f := f.algebra
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The coefficient projection is the literal constant-algebra functor on every original ring map. -/
def coefficientProjection (X : QcqsScheme) : Family X ⥤ SAlg ℤ :=
  ringProjection X ⋙ constantCoefficients

/-- Actual scheme pullback reindexes all ordinary affine tests by source-map composition. -/
def reindex {X Y : QcqsScheme} (f : X ⟶ Y) : Family X ⥤ Family Y where
  obj a := ⟨a.algebra, a.map ≫ f⟩
  map g := ⟨g.algebra, by rw [← Category.assoc, g.square]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)

/-- The actual whole ordinary QCoh category is the native full cocartesian section object. -/
def qcoh (X : QcqsScheme) : SSet.{1} :=
  sectionsOver M.projection (nerveMap (coefficientProjection X))

/-- Native section reindexing retains every original module arrow and every parameter simplex. -/
def qcohPullback {X Y : QcqsScheme} (f : X ⟶ Y) : qcoh M Y ⟶ qcoh M X :=
  sectionsOverMap M.projection (nerveMap (coefficientProjection Y))
    (nerveMap (coefficientProjection X)) (nerveMap (reindex f)) (by
      ext n a
      rfl)

/-- The same original affine module value is evaluated on the full section source. -/
def evaluateSection {X : QcqsScheme} (a : (qcoh M X) _⦋0⦌) (j : Family X) : M.total _⦋0⦌ :=
  (a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌))) (ComposableArrows.mk₀ j)

/-- Ordinary perfectness uses the original localized finite-cell/retract criterion in every constant coefficient fibre. -/
def IsPerfectGlobal (X : QcqsScheme) (a : (qcoh M X) _⦋0⦌) : Prop :=
  ∀ j : Family X, IsPerfectAt M ((coefficientProjection X).obj j) (evaluateSection M a j)

/-- Reindexing preserves the same actual perfect-module tests, with no field/finite-type restriction. -/
theorem perfect_pullback {X Y : QcqsScheme} (f : X ⟶ Y)
    (a : (qcoh M Y) _⦋0⦌) (ha : IsPerfectGlobal M Y a) :
    IsPerfectGlobal M X ((qcohPullback M f).app (op ⦋0⦌) a) := by
  intro j
  have hj := ha ((reindex f).obj j)
  change IsPerfectAt M ((coefficientProjection X).obj j)
    ((a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌)))
      ((nerveMap (reindex f)).app (op ⦋0⦌) (ComposableArrows.mk₀ j)))
  rw [nerveMap_app_mk₀]
  exact hj

/-- The full ordinary Perf category retains every coherent noninvertible module arrow. -/
def perf (X : QcqsScheme) : SSet.{1} :=
  ((qcoh M X).fullEnhancedSubcategory (IsPerfectGlobal M X)).toSSet

/-- The actual ordinary Perf pullback is the full native section-reindexing map. -/
def perfPullback {X Y : QcqsScheme} (f : X ⟶ Y) : perf M Y ⟶ perf M X :=
  SSet.Subcomplex.lift
    (((qcoh M Y).fullEnhancedSubcategory (IsPerfectGlobal M Y)).ι ≫ qcohPullback M f)
    (by
      rw [SSet.range_le_fullEnhancedSubcategory_iff]
      intro a
      exact perfect_pullback M f a.val
        ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff (IsPerfectGlobal M Y) a.val).mp a.property))

end MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
