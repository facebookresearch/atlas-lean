/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoHiggsModuliModels
public import MathlibExt.AlgebraicGeometry.AnalyticRealization
public import MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles

/-!
# Algebraic Higgs fibres and their actual analytic frames

The algebraic fibre is the pullback of the actual universal Higgs family
along C times a complex moduli point. A smooth bundle atlas is fixed by
the evaluated transition coefficients of that algebraic sheaf. Its Higgs
matrix is the evaluated actual twisted-field matrix times the realized
cotangent generator. Cotangent realization is fixed on every actual
universal differential by differentiation of regular-function evaluation.

Source: Hitchin, The self-duality equations on a Riemann surface (1987),
Sections 2 and 4; de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2,
Sections 1.2.2 and 1.2.4. Native analytic pullback and smooth-bundle
attribution and pinned revisions are retained in the imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoHiggsAnalyticFrames

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry TopologicalSpace
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels GeometricHiggsFamilies
open CoherentCurveLinearSeries LineBundleTaskContracts RelativeLambdaReindexing
open ComplexAnalytification KahlerClassGeometry SmoothHarmonicBundleGeometry
open DeligneFaltingsCategories
open scoped Manifold ContDiff Matrix

def pointMorphism {X : ComplexScheme} (p : ComplexPoints X.hom) :
    𝟙_ (Over (Spec (.of ℂ))) ⟶ X := Over.homMk p.hom p.hom_comp

def pointFamilyMap (C : ComplexScheme) {B : BaseChanges C} (M : ModuliModel C B)
    (p : ComplexPoints M.scheme.hom) : C ⟶ prod C M.scheme :=
  prod.lift (𝟙 C) (toUnit C ≫ pointMorphism p)

theorem pointFamilyMap_first (C : ComplexScheme) {B : BaseChanges C} (M : ModuliModel C B)
    (p : ComplexPoints M.scheme.hom) : pointFamilyMap C M p ≫ prod.fst = 𝟙 C := by
  simp [pointFamilyMap]

def pointLineComparison (C : ComplexScheme) {B : BaseChanges C} (M : ModuliModel C B)
    (p : ComplexPoints M.scheme.hom) :
    (Scheme.Modules.pullback (pointFamilyMap C M p).left).obj
      ((Scheme.Modules.pullback (prod.fst : prod C M.scheme ⟶ C).left).obj (canonicalLine C)) ≅
        canonicalLine C :=
  (Scheme.Modules.pullbackComp (pointFamilyMap C M p).left
    (prod.fst : prod C M.scheme ⟶ C).left).app (canonicalLine C) ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (pointFamilyMap_first C M p))).app (canonicalLine C) ≪≫
    (Scheme.Modules.pullbackId C.left).app (canonicalLine C)

structure HiggsPointModel (C : ComplexScheme) [IsProperCurve C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] {B : BaseChanges C}
    (M : ModuliModel C B) (p : ComplexPoints M.scheme.hom) where
  tensor : TensorPullbackComparison (pointFamilyMap C M p).left
  object : TwistedBundle C.left (canonicalLine C) 2
  module : object.module ≅
    (Scheme.Modules.pullback (pointFamilyMap C M p).left).obj M.universalFamily.obj.module
  field : object.field ≫ tensorMap module.hom (𝟙 (canonicalLine C)) =
    module.hom ≫ (Scheme.Modules.pullback (pointFamilyMap C M p).left).map
      M.universalFamily.obj.field ≫
      (tensor.iso M.universalFamily.obj.module
        ((Scheme.Modules.pullback (prod.fst : prod C M.scheme ⟶ C).left).obj
          (canonicalLine C))).hom ≫
      tensorMap (𝟙 _) (pointLineComparison C M p).hom
  degree : CurveVectorBundles.bundleDegree C.hom object.module 2 object.bundle = 1
  stable : IsStableCurve C object

/-- The native universal differential, exterior-degree-one inclusion and sheafification unit. -/
def algebraicDifferential (C : ComplexScheme) (U : C.left.Opens) (a : Γ(C.left, U)) :
    Γ(canonicalLine C, U) :=
  let D := AlgebraicDifferentialSheaves.differentials ℂ C
  let d := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (AlgebraicDifferentialSheaves.scalarMap ℂ C)).d a
  let w : ⋀[Γ(C.left, U)]^1 (D.obj (op U)) :=
    ⟨ExteriorAlgebra.ιMulti Γ(C.left, U) 1 (fun _ => d),
      ExteriorAlgebra.ιMulti_range Γ(C.left, U) 1 (Set.mem_range_self _)⟩
  (((moduleAdjunction C.left).unit.app
    (AlgebraicDifferentialSheaves.formsPresheaf ℂ C 1)).app (op U)).hom
      ((PresheafOfModules.extPowSections 1 D (op U)).symm w)

def regularEvaluation (C : ComplexScheme) (U : C.left.Opens) (a : Γ(C.left, U)) :
    space C → ℂ := by
  classical
  exact fun p => if h : p.Mem U then ComplexPoints.eval a p h else 0

variable (C : ComplexScheme) [AnalyticRealization.AnalyticManifold C 1]
  [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]

/-- Actual affine sheaf frames fix all smooth transition and Higgs matrices. -/
structure AnalyticFrames (E : TwistedBundle C.left (canonicalLine C) 2) where
  bundle : SmoothComplexBundle 1 (space C) 2
  higgs : HolomorphicHiggsField bundle
  chart : Fin bundle.count → C.left.Opens
  algebraic : ∀ i, AffineTwistedFrame E (chart i)
  cover : ∀ x : C.left, ∃ i, x ∈ chart i
  membership : ∀ (i : Fin bundle.count) (x : ComplexPoints C.hom),
    x ∈ bundle.core.baseSet i ↔ x.Mem (chart i)
  regularFunctions : ∀ i (a : Γ(C.left, chart i)),
    ContMDiffOn 𝓘(ℂ, Coordinates 1) 𝓘(ℂ, ℂ) ∞ (regularEvaluation C (chart i) a)
      {p | p.Mem (chart i)}
  overlapBasis : ∀ i j, Module.Basis (Fin 2) Γ(C.left, chart i ⊓ chart j)
    Γ(E.module, chart i ⊓ chart j)
  overlap_normalized : ∀ i j a, overlapBasis i j a =
    (E.module.val.map (homOfLE (show chart i ⊓ chart j ≤ chart i from inf_le_left)).op).hom
      ((algebraic i).basis a)
  transition : ∀ i j (x : ComplexPoints C.hom) (hx : x.Mem (chart i ⊓ chart j)),
    transitionMatrix bundle i j x = fun a b => ComplexPoints.eval
      ((overlapBasis i j).repr
        ((E.module.val.map
          (homOfLE (show chart i ⊓ chart j ≤ chart j from inf_le_right)).op).hom
            ((algebraic j).basis b)) a) x hx
  cotangent : Fin bundle.count → space C → Coordinates 1 →ₗ[ℂ] ℂ
  cotangent_nondegenerate : ∀ i (x : ComplexPoints C.hom), x.Mem (chart i) →
    Function.Bijective (cotangent i x)
  differential : ∀ i (a : Γ(C.left, chart i)) (x : ComplexPoints C.hom)
      (hx : x.Mem (chart i)) (u : Coordinates 1),
    ComplexPoints.eval ((algebraic i).lineBasis.repr (algebraicDifferential C (chart i) a) ())
      x hx * cotangent i x u =
      mfderivWithin 𝓘(ℂ, Coordinates 1) 𝓘(ℂ, ℂ) (regularEvaluation C (chart i) a)
        {p | p.Mem (chart i)} x u
  field : ∀ i (x : ComplexPoints C.hom) (hx : x.Mem (chart i)) (u : Coordinates 1),
    higgs.theta i x u = fun a b =>
      ComplexPoints.eval
        (LinearMap.toMatrix (algebraic i).basis (algebraic i).basis
          (framedEnd E (algebraic i)) a b) x hx * cotangent i x u

end MathlibExt.AlgebraicGeometry.RankTwoHiggsAnalyticFrames
