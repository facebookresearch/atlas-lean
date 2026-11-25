/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericSourceIndex
public import MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# The actual scaling differential in a generic Li source

Each Lie generator is the actual torus point with the unit 1 + epsilon
in that coordinate. Its deformation is an actual global map extension,
with the entire finite source curve obtained by trivial base change.
The source cochain is its image under the normalized Li deformation
classification. The quotient is the native mapping cone of this one
cochain map. Rank zero and empty component sets remain permitted.

Source: Jun Li math/0110113v1 Theorems 2.2--2.3, (2.1), and the scheme
torus actions of math/0009097v1 Sections 1 and 4.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGenericGaugeSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry
open LiGenericSourceModels LiGenericSourceIndex ExpansionParameterModels

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k] {X : Stack (Spec (.of k))} (C : SourceChart X)

abbrev coefficient := ModuleCat.of C.ring C.ring
abbrev rawComplex := C.source.complex (coefficient C)
abbrev target := Over.mk C.family.structural

/-- Freeze the module-category instances before a regular module is specialized. -/
def moduleSquareRing {A : Type} [CommRing A] (I : ModuleCat.{0} A) : CommRingCat.{0} :=
  .of (TrivSqZeroExt A I)

/-- The module-category coefficient ring is transported to the literal torus dual numbers. -/
def squareZeroRingIso : moduleSquareRing (coefficient C) ≃+* TrivSqZeroExt C.ring C.ring where
  toFun x := ⟨x.fst, x.snd⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change x.fst * y.snd + y.fst * x.snd = x.fst * y.snd + x.snd * y.fst
      rw [mul_comm y.fst x.snd]

def infinitesimalBase : Spec (moduleSquareRing (coefficient C)) ⟶
    (TorusInfinitesimalPoints.doubled (k := k) C.ring).left :=
  Spec.map (@CommRingCat.ofHom (TrivSqZeroExt C.ring C.ring) (moduleSquareRing (coefficient C))
    inferInstance (moduleSquareRing (coefficient C)).commRing (squareZeroRingIso C).symm.toRingHom)

def infinitesimalProjection := infinitesimalBase C ≫
  (TorusInfinitesimalPoints.projection (k := k) C.ring).left

set_option maxHeartbeats 1000000 in
-- The indexed curve and torus action records contain the complete source diagram.
structure Gauge where
  rank : ℕ
  torus : TorusTheory k rank
  action : letI := torus.group; ModObj (torusScheme k rank) (target C)
  extension : ∀ j : Fin rank, MapExtension C.family (coefficient C)
  source : ∀ j v, ((extension j).curve.component v).curve.X ≅
    pullback (C.family.curve v).π (infinitesimalProjection C)
  source_projection : ∀ j v, (source j v).hom ≫ pullback.snd
    (C.family.curve v).π (infinitesimalProjection C) =
      ((extension j).curve.component v).curve.π
  source_reduction : ∀ j v, ((extension j).curve.component v).reduction ≫
    (source j v).hom ≫ pullback.fst
      (C.family.curve v).π (infinitesimalProjection C) = 𝟙 _
  markings : ∀ j v i, ((extension j).curve.component v).curve.marking i ≫
    (source j v).hom ≫ pullback.fst
      (C.family.curve v).π (infinitesimalProjection C) =
        infinitesimalProjection C ≫ (C.family.curve v).marking i
  original : ∀ j v, Over.mk (((extension j).curve.component v).curve.π ≫
    infinitesimalBase C ≫ (TorusInfinitesimalPoints.doubled (k := k) C.ring).hom) ⟶ target C
  original_map : ∀ j v, (original j v).left = (source j v).hom ≫
    pullback.fst (C.family.curve v).π (infinitesimalProjection C) ≫ C.family.map v
  map : letI := torus.group; letI := action;
    ∀ j v, (extension j).map v =
      (CartesianMonoidalCategory.lift
        (Over.homMk (((extension j).curve.component v).curve.π ≫ infinitesimalBase C)
          (Category.assoc _ _ _) ≫
          TorusInfinitesimalPoints.point torus C.ring j)
        (original j v) ≫ γ[torusScheme k rank,target C]).left

abbrev lieComplex (G : Gauge C) :=
  (CochainComplex.singleFunctor (ModuleCat.{0} C.ring) 1).obj
    (ModuleCat.of C.ring (Fin G.rank → C.ring))

abbrev lieCoefficient (G : Gauge C) (I : ModuleCat.{0} C.ring) :=
  (CochainComplex.singleFunctor (ModuleCat.{0} C.ring) 1).obj
    (ModuleCat.of C.ring (Fin G.rank → I))

def coefficientPoint (I : ModuleCat.{0} C.ring) (x : I) : coefficient C ⟶ I :=
  ModuleCat.ofHom
    { toFun := fun a => a • x
      map_add' := fun a b => add_smul a b x
      map_smul' := by intro a b; change (a * b) • x = a • (b • x); exact mul_smul a b x }

/-- The cochain map is fixed on every actual torus generator. -/
structure Source where
  gauge : Gauge C
  map : lieComplex C gauge ⟶ rawComplex C
  normalized : ∀ j : Fin gauge.rank,
    (C.source.termIso (coefficient C) 1).hom
      (map.f 1 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
        (ModuleCat.of C.ring (Fin gauge.rank → C.ring))).inv (Pi.single j 1))) =
      ((C.deformations.functor (coefficient C)).obj (gauge.extension j)).value.val
  coefficientMap : ∀ I : ModuleCat.{0} C.ring, lieCoefficient C gauge I ⟶ C.source.complex I
  unit : coefficientMap (coefficient C) = map
  pure : ∀ (I : ModuleCat.{0} C.ring) (j : Fin gauge.rank) (x : I),
    (coefficientMap I).f 1
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
        (ModuleCat.of C.ring (Fin gauge.rank → I))).inv (Pi.single j x)) =
      (C.coefficients.map (coefficientPoint C I x)).f 1
        (map.f 1 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
          (ModuleCat.of C.ring (Fin gauge.rank → C.ring))).inv (Pi.single j 1)))

def quotientComplex (G : Source C) : CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  CochainComplex.mappingCone G.map

def quotientCoefficientComplex (G : Source C) (I : ModuleCat.{0} C.ring) :
    CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  CochainComplex.mappingCone (G.coefficientMap I)

end MathlibExt.AlgebraicGeometry.LiGenericGaugeSourceModels
