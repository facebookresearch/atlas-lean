/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
public import MathlibExt.CategoryTheory.DGScalarExtensionModels

/-!
# All native geometric perfect tests and their restricted DG Yoneda module

The perfect tests are the full DG subcategory of the actual small-etale
cochain category. They are K-injective and, on every actual affine etale
chart, their native derived restriction is a bounded finite-projective
coefficient complex. Quasi-coherence uses the same charts and the same
native associated-module functor, with arbitrary coefficient complexes.

The restricted Yoneda value at a perfect test is literally the full
native linear Hom complex. Pseudo-perfection tests the perfection of
every such coefficient Hom complex. This does not identify relatively
perfect or pseudo-perfect complexes with absolute perfect complexes on
a singular proper source.

References: Toen--Vaquie math/0503269v5, Section3.5 pp59--61, especially
Remark3.30(2); Stacks 03G8, 06YY and the native small-etale perfect source
at AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b. The actual
DG Yoneda, restrictions and native cochains retain their existing source
revision/license notices in the imported modules. Construction and
comparison proofs remain separate Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies

universe u

attribute [local instance] HasDerivedCategory.standard

/-- An actual affine etale chart, with its specified native affine scheme identification. -/
structure AffineSourceChart (X : SourceSpace.{u}) where
  chart : EtaleChart X
  ring : CommRingCat.{u}
  scheme_eq : chart.scheme = Spec ring

/-- An affine ordinary test of the actual proper source situation, retaining its native test scheme. -/
structure AffineProperFamily (D : ProperSpaceSituation.{u}) where
  test : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyTest D
  ring : CommRingCat.{u}
  scheme_eq : test.scheme = Spec ring

/-- The coefficient projection is the actual fixed source-family projection through that affine identification. -/
def affineProperProjection (D : ProperSpaceSituation.{u}) (T : AffineProperFamily D) :
    (familySpace D T.test).sheaf ⟶ represented.obj (Spec T.ring) :=
  familyProjection D T.test ≫ represented.map (eqToHom T.scheme_eq)

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
  (L : EtalePullbackSystem O)
  (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
  (R : ChartRestrictionSystem O)

/-- This restriction is the existing native chart functor followed by the actual affine identification. -/
def affineChartRestriction {X : SourceSpace.{u}} (C : AffineSourceChart X) :
    Derived X ⥤ EtaleDerived O (Spec C.ring) :=
  chartDerivedRestriction (R.chart X C.chart) ⋙
    etaleDerivedPullback (L.derived (eqToHom C.scheme_eq.symm))

/-- Quasi-coherence is tested in the essential image of the literal native affine associated-complex functor. -/
def IsSourceQuasiCoherent {X : SourceSpace.{u}} (E : Derived X) : Prop :=
  ∀ C : AffineSourceChart X,
    ∃ K : CochainComplex (ModuleCat.{u} C.ring) ℤ,
      Nonempty ((affineChartRestriction O L R C).obj E ≅ associatedEtaleDerived (J C.ring) K)

/-- Absolute perfection uses finite projectivity over the actual chart ring, in every degree. -/
def IsSourcePerfect {X : SourceSpace.{u}} (E : Derived X) : Prop :=
  ∀ C : AffineSourceChart X,
    ∃ K : StrictPerfectComplex C.ring,
      Nonempty ((affineChartRestriction O L R C).obj E ≅ associatedEtaleDerived (J C.ring) K.complex)

/-- The same finite-projective presentations are actual quasi-coherent presentations. -/
theorem sourcePerfect_quasiCoherent {X : SourceSpace.{u}} {E : Derived X}
    (h : IsSourcePerfect O L J R E) : IsSourceQuasiCoherent O L J R E := by
  intro C
  obtain ⟨K, e⟩ := h C
  exact ⟨K.complex, e⟩

variable {X : SourceSpace.{u}} {A : CommRingCat.{u}}
  {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π)

/-- Native source quasi-coherent cochains, with K-injectivity in the same source module category. -/
def qcohProperty : (geometricDG S) → Prop :=
  fun K => (show CochainComplex (Modules X) ℤ from K).IsKInjective ∧
    IsSourceQuasiCoherent O L J R
      (DerivedCategory.Q.obj (show CochainComplex (Modules X) ℤ from K))

/-- Native source perfect cochains, retaining finite-projective affine tests rather than relative perfection. -/
def perfectProperty : (geometricDG S) → Prop :=
  fun K => (show CochainComplex (Modules X) ℤ from K).IsKInjective ∧
    IsSourcePerfect O L J R
      (DerivedCategory.Q.obj (show CochainComplex (Modules X) ℤ from K))

/-- The actual full geometric quasi-coherent DG category and its complete native Hom complexes. -/
def qcohDGCategory : DGCat (LargeScalar A) :=
  DGCat.of (LargeScalar A) (DGFullSubcategory (qcohProperty O L J R S))

/-- All actual geometric perfect tests, in the original native DG enrichment. -/
def perfectDGCategory : DGCat (LargeScalar A) :=
  DGCat.of (LargeScalar A) (DGFullSubcategory (perfectProperty O L J R S))

/-- The actual full inclusion retains every original homogeneous source cochain. -/
def perfectIntoQCoh : perfectDGCategory O L J R S ⟶ qcohDGCategory O L J R S where
  obj K := ⟨K.obj, K.property.1, sourcePerfect_quasiCoherent O L J R K.property.2⟩
  map _ _ := 𝟙 _

/-- The restricted Yoneda module evaluates against every actual perfect complex, not a chosen compact generator. -/
def allPerfectTestsYoneda (E : qcohDGCategory O L J R S) :
    RightModule (LargeScalar A) (perfectDGCategory O L J R S) :=
  restrictModule (perfectIntoQCoh O L J R S) ((dgYoneda (LargeScalar A)).obj E)

/-- Each actual module value is the original full geometric linear Hom cochain complex. -/
theorem allPerfectTestsYoneda_value (E : qcohDGCategory O L J R S)
    (P : (perfectDGCategory O L J R S)ᵒᵖ) :
    (allPerfectTestsYoneda O L J R S E).toEnrichedFunctor.obj P =
      dgHomComplex (LargeScalar A) P.unop.obj E.obj := rfl

/-- Perfection of a coefficient cochain is an actual bounded finite-projective presentation in its derived category. -/
def IsPerfectCoefficientCochain (K : Cochains (LargeScalar A)) : Prop :=
  ∃ P : StrictPerfectComplex (CommRingCat.of (LargeScalar A)),
    Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj P.complex)

/-- Source pseudo-perfection uses every native perfect test and the actual A-linear Hom complex. -/
def IsSourcePseudoPerfect (E : qcohDGCategory O L J R S) : Prop :=
  ∀ P : perfectDGCategory O L J R S,
    IsPerfectCoefficientCochain (A := A) (dgHomComplex (LargeScalar A) P.obj E.obj)

/-- Pseudo-perfection is literally objectwise coefficient perfection of this fixed restricted Yoneda module. -/
theorem sourcePseudoPerfect_iff_allPerfectTests (E : qcohDGCategory O L J R S) :
    IsSourcePseudoPerfect O L J R S E ↔
      ∀ P : perfectDGCategory O L J R S,
        IsPerfectCoefficientCochain (A := A)
          ((allPerfectTestsYoneda O L J R S E).toEnrichedFunctor.obj (op P)) := Iff.rfl

/-- A small source model is connected to all of the actual perfect tests by the complete lifted DG realization. -/
structure SmallPerfectTestModel (C : CochainLiftModel A) where
  category : DGCat A
  realization : EnrichedFunctor (Cochains (LargeScalar A)) (liftedDGCategory C category)
    (perfectDGCategory O L J R S)
  quasiEquivalence : realization.IsQuasiEquivalence

end MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
