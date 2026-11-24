/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
public import MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
public import MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Actual rank-two degree-one stable Higgs families

The twist is the actual cotangent sheaf of the fixed smooth projective
complex curve. Families reuse the native twisted-bundle groupoid and
invariant saturated-subbundle slope stability. Every geometric fibre is
the actual pulled family, with the tensor comparison fixed on native
sections. Degree one is imposed on those actual fibres.

Reindexing, arrows, units and composition retain the actual sheaf
pullback comparisons. No Chern-class vanishing is required.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Sections1.2.2--1.3.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RankTwoHiggsCurveFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open GeometricHiggsFamilies RelativeLambdaReindexing CoherentCurveLinearSeries
open CurveVectorBundles LineBundleTaskContracts

abbrev ComplexScheme := Over (Spec (.of ℂ))

def canonicalLine (C : ComplexScheme) : C.left.Modules := IntegrableHiggsBundles.Omega C 1

class CurveSource (C : ComplexScheme) extends PerverseSheaves.IsComplexVariety C where
  smooth : Smooth C.hom
  connected : ConnectedSpace C.left
  projective : ProjectiveSpace.IsProjective C
  cotangentLine : IsLineBundle (canonicalLine C)
  [smoothCurve : SmoothOfRelativeDimension 1 C.hom]
  [properCurve : IsProperCurve C.hom]
  [integral : IsIntegral C.left]
  genusRange : 2 ≤ genus C.hom

attribute [instance] CurveSource.smooth CurveSource.connected CurveSource.smoothCurve
  CurveSource.properCurve CurveSource.integral

abbrev Family (C T : ComplexScheme) := CurveFamily C T (canonicalLine C) 2

def curveMap (C : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T) : prod C S ⟶ prod C T :=
  prod.map (𝟙 C) f

theorem curveMap_first (C : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T) :
    curveMap C f ≫ (prod.fst : prod C T ⟶ C) = prod.fst := by simp [curveMap]

theorem curveMap_id (C T : ComplexScheme) : curveMap C (𝟙 T) = 𝟙 (prod C T) := by
  simp [curveMap]

theorem curveMap_comp (C : ComplexScheme) {R S T : ComplexScheme} (f : R ⟶ S) (g : S ⟶ T) :
    curveMap C f ≫ curveMap C g = curveMap C (f ≫ g) := by
  apply prod.hom_ext <;> simp [curveMap]

def lineReindex (C : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T) :
    (Scheme.Modules.pullback (curveMap C f).left).obj
      ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C)) ≅
    (Scheme.Modules.pullback (prod.fst : prod C S ⟶ C).left).obj (canonicalLine C) :=
  (Scheme.Modules.pullbackComp (curveMap C f).left (prod.fst : prod C T ⟶ C).left).app _ ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (curveMap_first C f))).app _

structure FamilyPullback (C : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T)
    (E : Family C T) (E' : Family C S) (P : TensorPullbackComparison (curveMap C f).left) where
  comparison : E'.module ≅ (Scheme.Modules.pullback (curveMap C f).left).obj E.module
  field : E'.field ≫ tensorMap comparison.hom
      (𝟙 ((Scheme.Modules.pullback (prod.fst : prod C S ⟶ C).left).obj (canonicalLine C))) =
    comparison.hom ≫ (Scheme.Modules.pullback (curveMap C f).left).map E.field ≫
      (P.iso E.module
        ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C))).hom ≫
      tensorMap (𝟙 _) (lineReindex C f).hom

def complexField (Ω : Type) [Field Ω] [Algebra ℂ Ω] : ComplexScheme :=
  Over.mk (Spec.algebraMap ℂ Ω)

def curveOverField (C : ComplexScheme) (Ω : Type) [Field Ω] [Algebra ℂ Ω] :
    Over (Spec (.of Ω)) :=
  Over.mk (prod.snd : prod C (complexField Ω) ⟶ complexField Ω).left

/-- Every geometric fibre of the family is a stable bundle of rank two and degree one on the
base-changed curve, which is a smooth proper integral curve. -/
def Admissible (C T : ComplexScheme) : ObjectProperty (Family C T) := fun E =>
  ∀ (Ω : Type) [Field Ω] [Algebra ℂ Ω] [IsAlgClosed Ω] (x : complexField Ω ⟶ T),
    ∃ (_ : IsProperCurve (curveOverField C Ω).hom)
      (_ : SmoothOfRelativeDimension 1 (curveOverField C Ω).hom)
      (_ : IsIntegral (curveOverField C Ω).left),
    ∃ P : TensorPullbackComparison (curveMap C x).left,
    ∃ E' : Family C (complexField Ω),
    Nonempty (FamilyPullback C x E E' P) ∧
      bundleDegree (curveOverField C Ω).hom E'.module 2 E'.bundle = 1 ∧
      IsStableCurve (curveOverField C Ω) E'

abbrev StableFamily (C T : ComplexScheme) := (Admissible C T).FullSubcategory

structure BaseChanges (C : ComplexScheme) where
  tensor : ∀ {S T : ComplexScheme} (f : S ⟶ T), TensorPullbackComparison (curveMap C f).left
  change : ∀ {S T : ComplexScheme} (_f : S ⟶ T), StableFamily C T ⥤ StableFamily C S
  models : ∀ {S T : ComplexScheme} (f : S ⟶ T) (E : StableFamily C T),
    FamilyPullback C f E.obj ((change f).obj E).obj (tensor f)
  arrows : ∀ {S T : ComplexScheme} (f : S ⟶ T) {E E' : StableFamily C T} (a : E ⟶ E'),
    ((change f).map a).hom.iso.hom ≫ (models f E').comparison.hom =
      (models f E).comparison.hom ≫ (Scheme.Modules.pullback (curveMap C f).left).map a.hom.iso.hom
  unit : ∀ T : ComplexScheme, change (𝟙 T) ≅ 𝟭 (StableFamily C T)
  unit_normalized : ∀ (T : ComplexScheme) (E : StableFamily C T),
    ((unit T).hom.app E).hom.iso.hom =
      (models (𝟙 T) E).comparison.hom ≫
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (curveMap_id C T))).hom.app E.obj.module ≫
      (Scheme.Modules.pullbackId (prod C T).left).hom.app E.obj.module
  composition : ∀ {R S T : ComplexScheme} (f : R ⟶ S) (g : S ⟶ T),
    change g ⋙ change f ≅ change (f ≫ g)
  composition_normalized : ∀ {R S T : ComplexScheme} (f : R ⟶ S) (g : S ⟶ T)
      (E : StableFamily C T),
    ((composition f g).hom.app E).hom.iso.hom ≫ (models (f ≫ g) E).comparison.hom =
      (models f ((change g).obj E)).comparison.hom ≫
      (Scheme.Modules.pullback (curveMap C f).left).map (models g E).comparison.hom ≫
      (Scheme.Modules.pullbackComp (curveMap C f).left (curveMap C g).left).hom.app E.obj.module ≫
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (curveMap_comp C f g))).hom.app E.obj.module

end MathlibExt.AlgebraicGeometry.RankTwoHiggsCurveFamilies
