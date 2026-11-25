/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons
public import MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import MathlibExt.CategoryTheory.DGScalarExtensionModels
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Whole polynomial diagrams and their actual exterior coefficient span

The replacement is projectively cofibrant in the category of entire
algebra diagrams. Its original augmentation to the affine algebra
projection and its lift to QA form one actual augmentation square.
Every polynomial and simplicial form generator is retained.

Both sides of the comparison span are actual native modules: the
balanced exterior module on QQ and its derived scalar extension to A.
The unit is the unit of the full enriched extension/restriction
adjunction. The other leg applies the original QQ to QA form map and
the original QA weight shift. All module, coefficient, parameter and
refinement arrows are maps of the complete diagrams.

Sources: PTVV arXiv:1111.3209v4, Proposition 1.14 and Lemma 1.15;
HAG II arXiv:math/0404373v7, Sections 1.3.7 and 1.4.1. The native
DG module, polynomial, normalization and exterior notices are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedResolvedExteriorDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open CochainComplex.HomComplex
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {X : Prestack k} {N : ShuffleAlgebraFunctor k} {L : CochainLiftModel k}

/-- The projective lifting criterion concerns complete algebra diagrams,
including all family and simplex arrows. -/
def IsProjectivelyCofibrantAlgebraDiagram (T : Families X ⥤ SAlg k) : Prop :=
  ∀ (A B : Families X ⥤ SAlg k) (p : A ⟶ B),
    (∀ j, IsAlgebraTrivialFibration (p.app j)) →
      ∀ f : T ⟶ B, ∃ g : T ⟶ A, g ≫ p = f

/-- QQ retains its original whole-diagram augmentation and actual QQ to QA square. -/
structure PolynomialAlgebraDiagram (Q : AlgebraReplacementFunctor k) (X : Prestack k) where
  algebra : Families X ⥤ SAlg k
  cofibrant : IsProjectivelyCofibrantAlgebraDiagram algebra
  augmentation : algebra ⟶ algebraProjection X
  trivialFibration : ∀ j, IsAlgebraTrivialFibration (augmentation.app j)
  generators : Families X → SimplexCategoryᵒᵖ → Type u
  polynomial : ∀ (j : Families X) (n : SimplexCategoryᵒᵖ),
    MvPolynomial (generators j n) k ≃ₐ[k] (algebra.obj j).obj n
  toQA : algebra ⟶ algebraProjection X ⋙ Q.functor
  square : toQA ≫ Functor.whiskerLeft (algebraProjection X) Q.augmentation = augmentation

/-- The QQ coefficient enrichment has an actual summand for every family arrow. -/
def algebraCoefficientGenerator {T : Families X ⥤ SAlg k}
    [DGCategory (LargeScalar k) (Families X)]
    (H : ∀ j l : Families X, dgHomComplex (LargeScalar k) j l ≅
      ∐ (fun _f : j ⟶ l => affineCoefficient L N (T.obj l)))
    {j l : Families X} (f : j ⟶ l) (p : ℤ)
    (a : (affineCoefficient L N (T.obj l)).X p) : DGHom (LargeScalar k) p j l :=
  (((Sigma.ι (fun _f : j ⟶ l => affineCoefficient L N (T.obj l)) f ≫
    (H j l).inv).f p).hom a)

/-- The enrichment is fixed on every actual homogeneous arrow generator. -/
structure AlgebraDiagramCoefficientCategory (L : CochainLiftModel k)
    (N : ShuffleAlgebraFunctor k) (T : Families X ⥤ SAlg k) where
  [enrichment : DGCategory (LargeScalar k) (Families X)]
  homIso : ∀ j l : Families X, dgHomComplex (LargeScalar k) j l ≅
    ∐ (fun _f : j ⟶ l => affineCoefficient L N (T.obj l))
  identity : ∀ j : Families X,
    dgId (LargeScalar k) j =
      algebraCoefficientGenerator homIso (𝟙 j) 0
        (dgId (LargeScalar k) (op (coefficientObject L N (T.obj j))))
  composition : ∀ (j l z : Families X) (f : j ⟶ l) (g : l ⟶ z)
    (p q r : ℤ) (h : p + q = r)
    (a : (affineCoefficient L N (T.obj l)).X p)
    (b : (affineCoefficient L N (T.obj z)).X q),
    dgComp (LargeScalar k)
      (algebraCoefficientGenerator homIso f p a)
      (algebraCoefficientGenerator homIso g q b) h =
      algebraCoefficientGenerator homIso (f ≫ g) r
        (dgComp (LargeScalar k) (((affineCoefficientMap L N (T.map g)).f p).hom a) b h)

/-- Every QQ coefficient generator retains its family arrow and its homogeneous degree. -/
def algebraGenerator {T : Families X ⥤ SAlg k}
    (C : AlgebraDiagramCoefficientCategory L N T) {j l : Families X}
    (f : j ⟶ l) (p : ℤ) (a : (affineCoefficient L N (T.obj l)).X p) :
    letI := C.enrichment; DGHom (LargeScalar k) p j l := by
  letI := C.enrichment
  exact algebraCoefficientGenerator C.homIso f p a

/-- The source and target are full native QQ coefficient sections. -/
abbrev AlgebraCoefficientSection {T : Families X ⥤ SAlg k}
    (C : AlgebraDiagramCoefficientCategory L N T) :=
  letI := C.enrichment
  DGFunctor (LargeScalar k) (Families X) (Cochains (LargeScalar k))

/-- Forgetting a QQ section keeps every value, every arrow and every native DG component. -/
structure AlgebraSectionDiagrams {T : Families X ⥤ SAlg k}
    (C : AlgebraDiagramCoefficientCategory L N T) where
  functor : AlgebraCoefficientSection C ⥤ (Families X ⥤ Cochains (LargeScalar k))
  value : letI := C.enrichment
    ∀ (E : AlgebraCoefficientSection C) (j : Families X),
    (functor.obj E).obj j = E.toEnrichedFunctor.obj j
  transport : letI := C.enrichment
    ∀ (E : AlgebraCoefficientSection C) (j l : Families X) (f : j ⟶ l),
    HEq (Cochain.ofHom ((functor.obj E).map f))
      (E.toEnrichedFunctor.dgMap 0 (algebraGenerator C f 0
        (dgId (LargeScalar k) (op (coefficientObject L N (T.obj l))))))
  map : letI := C.enrichment
    ∀ (E F : AlgebraCoefficientSection C) (f : E ⟶ F) (j : Families X),
    HEq ((functor.map f).app j) (evaluationMap f j)

/-- A polynomial exterior module uses the actual balanced tensor and its native skew image. -/
structure PolynomialExteriorModule [Algebra ℚ k] (N : ShuffleAlgebraFunctor k)
    (A : SAlg k) (F : SimplicialDRModel A) where
  cotangent : DGDerivedModules k (coefficientCategory N A)
  cotangentValue : value (coefficientCategory N A) PUnit.unit cotangent.obj ≅ normalizedForms F 1
  cotangentAction : ∀ (p q : ℕ)
    (a : (N.functor.obj A).X.X (-(p : ℤ)))
    (z : (value (coefficientCategory N A) PUnit.unit cotangent.obj).X (-(q : ℤ))),
    formCoefficient F 1 (p + q)
      ((cotangentValue.hom.f (-((p + q : ℕ) : ℤ))).hom
        (DerivedCotangentModels.moduleAction cotangent.obj (op PUnit.unit) a (by omega) z)) =
      formScalarShuffle F p q
        (MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle.coefficient A p
          (((N.model A).complexIso.hom.f (-(p : ℤ))).hom a))
        (formCoefficient F 1 q ((cotangentValue.hom.f (-(q : ℤ))).hom z))
  tensor : DerivedTensorModel (coefficientCategory N A) PUnit.unit
  unit : DGDerivedModules k (coefficientCategory N A)
  unit_eq : unit.obj = regularModule (coefficientCategory N A) PUnit.unit
  coherence : CoherenceModel (coefficientCategory N A) PUnit.unit tensor unit unit_eq
  exterior : ModuleExteriorSquare (coefficientCategory N A) PUnit.unit
    tensor unit unit_eq coherence cotangent
  wedge : NormalizedFormWedge F
  formMap : value (coefficientCategory N A) PUnit.unit exterior.module.obj ⟶ normalizedForms F 2
  balanced : quotientMap (coefficientCategory N A) PUnit.unit
      (tensor.action cotangent.obj) (tensor.action cotangent.obj) ≫
    (tensor.value cotangent cotangent).comparison.inv ≫
    moduleComponent ((DGFunctor.homEquivDGCycles k _ _).symm
      ⟨exterior.projection, exterior.projection_closed⟩) (op PUnit.unit) ≫ formMap =
      (cotangentValue.hom ⊗ₘ cotangentValue.hom) ≫ wedge.map

/-- Native extension of the QQ exterior coefficient is evaluated at the actual coefficient object. -/
def exteriorScalarUnit {A B : SAlg k} (f : A ⟶ B)
    (R : RestrictionModel (coefficientMap N f)) (S : ExtensionModel (coefficientMap N f) R)
    (P : DGDerivedModules k (coefficientCategory N A)) :
    value (coefficientCategory N A) PUnit.unit P.obj ⟶
      value (coefficientCategory N B) PUnit.unit (S.functor.obj P).obj :=
  moduleComponent (closedModuleMap (S.unit P) (S.unit_closed P)) (op PUnit.unit) ≫
    (restrictionPointValueIso (coefficientMap N f) rfl R (S.functor.obj P).obj).hom

/-- The span consists of actual polynomial modules and actual derived scalar extensions;
its arrows are normalized on whole diagrams, with their original source augmentations. -/
structure PolynomialExteriorSpan [Algebra ℚ k] (D : AffineDRSystem Q)
    (P : PolynomialAlgebraDiagram Q X) where
  forms : ∀ j : Families X, SimplicialDRModel (P.algebra.obj j)
  formTransport : ∀ {j l : Families X} (f : j ⟶ l),
    SimplicialDRMap (forms j) (forms l) (P.algebra.map f)
  modules : ∀ j : Families X, PolynomialExteriorModule N (P.algebra.obj j) (forms j)
  polynomialFamily : Families X ⥤ AffineModulePoint N
  polynomialBase : polynomialFamily ⋙ moduleProjection N = P.algebra
  polynomialObject : ∀ j : Families X,
    polynomialFamily.obj j = AffineModulePoint.mk (P.algebra.obj j) (modules j).exterior.module.obj
  formDiagram : Families X ⥤ Cochains (LargeScalar k)
  formObject : ∀ j, formDiagram.obj j = (largeCochainLift k).obj (normalizedForms (forms j) 2)
  formArrow : ∀ {j l : Families X} (f : j ⟶ l),
    HEq (formDiagram.map f) ((largeCochainLift k).map (normalizedFormMap (formTransport f) 2))
  formComparison : rawCoefficientDiagram polynomialFamily ⟶ formDiagram
  formComparison_normalized : ∀ j,
    formComparison.app j =
      eqToHom (congrArg (fun V : AffineModulePoint N => (largeCochainLift k).obj V.value)
        (polynomialObject j)) ≫ (largeCochainLift k).map (modules j).formMap ≫
          eqToHom (formObject j).symm
  restriction : ∀ j, RestrictionModel (coefficientMap N (P.augmentation.app j))
  extension : ∀ j, ExtensionModel (coefficientMap N (P.augmentation.app j)) (restriction j)
  scalarFamily : Families X ⥤ AffineModulePoint N
  scalarBase : scalarFamily ⋙ moduleProjection N = algebraProjection X
  scalarObject : ∀ j,
    scalarFamily.obj j = AffineModulePoint.mk ((algebraProjection X).obj j)
      ((extension j).functor.obj (modules j).exterior.module).obj
  scalarUnit : rawCoefficientDiagram polynomialFamily ⟶ rawCoefficientDiagram scalarFamily
  scalarUnit_normalized : ∀ j,
    scalarUnit.app j =
      eqToHom (congrArg (fun V : AffineModulePoint N => (largeCochainLift k).obj V.value)
        (polynomialObject j)) ≫
      (largeCochainLift k).map
        (exteriorScalarUnit (P.augmentation.app j) (restriction j) (extension j)
          (modules j).exterior.module) ≫
      eqToHom (congrArg (fun V : AffineModulePoint N => (largeCochainLift k).obj V.value)
        (scalarObject j)).symm
  qaForms : ∀ j, SimplicialDRMap (forms j) (D.forms ((algebraProjection X).obj j)) (P.toQA.app j)
  toQA : formDiagram ⟶
    weightDiagram D 2 X ⋙ (globalToCoefficients k ⋙ shiftFunctor (Cochains (LargeScalar k)) (-2 : ℤ))
  toQA_normalized : ∀ j,
    toQA.app j = eqToHom (formObject j) ≫
      (largeCochainLift k).map (normalizedFormMap (qaForms j) 2) ≫
        affineCoefficientFormMap D ((algebraProjection X).obj j)

/-- The QA leg is the actual balanced polynomial comparison followed by QQ to QA and the weight shift. -/
def polynomialToQA [Algebra ℚ k] {D : AffineDRSystem Q}
    {P : PolynomialAlgebraDiagram Q X} (S : PolynomialExteriorSpan (N := N) D P) :=
  S.formComparison ≫ S.toQA

end MathlibExt.AlgebraicGeometry.DerivedResolvedExteriorDiagrams
