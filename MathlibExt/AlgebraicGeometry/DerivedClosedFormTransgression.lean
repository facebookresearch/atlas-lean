/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
public import MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
public import MathlibExt.AlgebraicGeometry.DerivedOrientationModels
public import MathlibExt.Algebra.Homology.ShiftedTensorUnits

/-!
# Native NC integration and literal evaluation transgression

Integration applies the actual weighted NC localization functor to
the relative mixed class, inverts the canonical finite-coefficient
NC comparison, and tensors with the actual scalar trace. Its final
unit/shift map retains the native homogeneous sign.

A cochain representative is normalized to that derived morphism in
the actual global NC complexes. Transgression is then the literal
evaluation pullback followed by this integration. Native shift
composition fixes the output degree n-d, for every integer degree.
No map producing a closed form is included in a geometric provider.

References: PTVV arXiv:1111.3209v4, Definition 2.3 and Theorem 2.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
attribute [local instance] HasDerivedCategory.standard

/-- The scalar regular-module value is the literal native coefficient unit. -/
def scalarRegularValueIso (R : Type u) [CommRing R] :
    value (scalarCategory R) PUnit.unit (regularModule (scalarCategory R) PUnit.unit) ≅
      (𝟙_ (Cochains R)) := Iso.refl _

/-- The genuine cochain trace on the actual cofibrant RΓ coefficient module. -/
def gammaTrace {k : Type u} [CommRing k] {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k} {V : NerveLiftModel L}
    {X : Prestack k} (A : FamilyModel M U Q L V X) (G : QCohEnhancement M U X)
    (D : ScalarGlobalModels A G) {d : ℤ} (T : TraceSystem A G D d) :
    gammaCoefficients A G D ⟶ (𝟙_ (Cochains (LargeScalar k)))⟦-d⟧ :=
  moduleToShift PUnit.unit T.source T.source_closed ≫
    (shiftFunctor (Cochains (LargeScalar k)) (-d)).map (scalarRegularValueIso (LargeScalar k)).hom

/-- The actual NC localization class is followed by the canonical comparison and id⊗trace. -/
def integrateClass {R : Type u} [CommRing R] {p : ℤ} (N : NCCategoryModel R p)
    {E F : GradedMixed R} {C : Cochains R} (P : PureTensorModel F C)
    (κ : (mixedQ R).obj E ⟶ (mixedQ R).obj P.mixed)
    (B : Comparison P p (N.diagram.toModel F) (N.diagram.toModel P.mixed))
    [IsIso (DerivedCategory.Q.map B.map)] {d : ℤ}
    (trace : C ⟶ (𝟙_ (Cochains R))⟦-d⟧)
    (U : UnitTensorModel (N.diagram.complex.obj F) (-d)) :
    DerivedCategory.Q.obj (N.diagram.complex.obj E) ⟶
      DerivedCategory.Q.obj ((N.diagram.complex.obj F)⟦-d⟧) :=
  (derivedNCObjIso N E).inv ≫ (derivedNC N).map κ ≫ (derivedNCObjIso N P.mixed).hom ≫
    inv (DerivedCategory.Q.map B.map) ≫
    DerivedCategory.Q.map (𝟙 (N.diagram.complex.obj F) ⊗ₘ trace) ≫
    DerivedCategory.Q.map U.comparison.hom

/-- The ordinary-form integration class uses the same actual κ, trace and native shift. -/
def integrateWeightClass {R : Type u} [CommRing R] (p : ℤ)
    {E F : GradedMixed R} {C : Cochains R} (P : PureTensorModel F C)
    (κ : (mixedQ R).obj E ⟶ (mixedQ R).obj P.mixed) {d : ℤ}
    (trace : C ⟶ (𝟙_ (Cochains R))⟦-d⟧) (U : UnitTensorModel (F.weight p) (-d)) :
    DerivedCategory.Q.obj (E.weight p) ⟶ DerivedCategory.Q.obj ((F.weight p)⟦-d⟧) :=
  (derivedWeightObjIso R p E).inv ≫ (derivedWeight R p).map κ ≫
    (derivedWeightObjIso R p P.mixed).hom ≫ DerivedCategory.Q.map (P.weightIso p).hom ≫
    DerivedCategory.Q.map (𝟙 (F.weight p) ⊗ₘ trace) ≫ DerivedCategory.Q.map U.comparison.hom

/-- The global NC bridge uses only the fixed actual limit lift and complete NC coefficient iso. -/
def globalNCToFunctor {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {L : CochainLiftModel k} {T : MixedLiftModel L} {p : ℕ}
    {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    {G : GlobalMixedModel D T X} {B : LiftedNCDiagram D T p N}
    {I : ReplacementNCDiagram G B} (H : MixedLimitNC I) {F : GlobalNCModel D p N X}
    (A : GlobalNCLift I F) (C : NCCategoryModel (LargeScalar k) (p : ℤ)) :
    (globalToCoefficients k).obj (ncComplex F) ⟶ C.diagram.complex.obj G.mixed :=
  globalNCComparison H A ≫ (ncModelIso H.model (C.diagram.toModel G.mixed)).hom

/-- Scalar restriction retains the same native shifted cochain object. -/
def coefficientShiftIso {k : Type u} [CommRing k] (K : GlobalComplex k) (n : ℤ) :
    (globalToCoefficients k).obj (K⟦n⟧) ≅ ((globalToCoefficients k).obj K)⟦n⟧ := Iso.refl _

/-- A native global cochain representative is normalized to a specified actual
derived NC morphism. The integration constructor supplies that computed morphism. -/
structure NCIntegrationRepresentative {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} (GP : GlobalNCModel D p N (F ⊗ X)) (GF : GlobalNCModel D p N F)
    (d : ℤ)
    (formula : DerivedCategory.Q.obj ((globalToCoefficients k).obj (ncComplex GP)) ⟶
      DerivedCategory.Q.obj (((globalToCoefficients k).obj (ncComplex GF))⟦-d⟧)) where
  map : ncComplex GP ⟶ (ncComplex GF)⟦-d⟧
  normalized : DerivedCategory.Q.map ((globalToCoefficients k).map map) ≫
    DerivedCategory.Q.map (coefficientShiftIso (ncComplex GF) (-d)).hom = formula

/-- The native cochain map retains the exact two shifts n-p and -d. -/
def shiftIntegrationCochain {k : Type u} [CommRing k] {K L : GlobalComplex k} {d : ℤ}
    (f : K ⟶ L⟦-d⟧) (p : ℕ) (n : ℤ) : K⟦n - (p : ℤ)⟧ ⟶ L⟦(n - d) - (p : ℤ)⟧ :=
  (shiftFunctor (GlobalComplex k) (n - (p : ℤ))).map f ≫
    (shiftFunctorAdd' (GlobalComplex k) (-d) (n - (p : ℤ)) ((n - d) - (p : ℤ))
      (by omega)).inv.app L

/-- The actual cochain integration shifts n-p to n-d-p through native shift composition. -/
def closedIntegration {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} {GP : GlobalNCModel D p N (F ⊗ X)} {GF : GlobalNCModel D p N F}
    {d : ℤ} {formula} (I : NCIntegrationRepresentative GP GF d formula) (n : ℤ) :
    closedSpace GP n ⟶ closedSpace GF (n - d) :=
  (realize k).map
    (shiftIntegrationCochain I.map p n)

/-- Integration fixes the actual zero of the full closing-data complex. -/
theorem closedIntegration_zero {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} {GP : GlobalNCModel D p N (F ⊗ X)} {GF : GlobalNCModel D p N F}
    {d : ℤ} {formula} (I : NCIntegrationRepresentative GP GF d formula) (n : ℤ) :
    (closedIntegration I n).app (op ⦋0⦌) (zeroForm GP n) = zeroForm GF (n - d) :=
  realize_map_zero _

/-- Transgression is literally the source evaluation pullback followed by integration. -/
def transgression {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} {R : FibrantReplacement F} (E : EvaluationModel Q X F R)
    (GT : GlobalNCModel D p N R.model)
    {GP : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R ⊗ X)}
    {GF : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R)}
    {d : ℤ} {formula} (I : NCIntegrationRepresentative GP GF d formula) (n : ℤ) :
    closedSpace GT n ⟶ closedSpace GF (n - d) :=
  closedPullback E.map GT GP n ≫ closedIntegration I n

/-- Every closed form, including all its closing coefficients, uses that same literal composite. -/
def transgressForm {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} {R : FibrantReplacement F} (E : EvaluationModel Q X F R)
    (GT : GlobalNCModel D p N R.model)
    {GP : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R ⊗ X)}
    {GF : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R)}
    {d : ℤ} {formula} (I : NCIntegrationRepresentative GP GF d formula) (n : ℤ)
    (ω : ClosedForm GT n) : ClosedForm GF (n - d) :=
  (transgression E GT I n).app (op ⦋0⦌) ω

theorem transgressForm_zero {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)}
    {F X : Prestack k} {R : FibrantReplacement F} (E : EvaluationModel Q X F R)
    (GT : GlobalNCModel D p N R.model)
    {GP : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R ⊗ X)}
    {GF : GlobalNCModel D p N (mappingPrestackFunctor k Q X F R)}
    {d : ℤ} {formula} (I : NCIntegrationRepresentative GP GF d formula) (n : ℤ) :
    transgressForm E GT I n (zeroForm GT n) = zeroForm GF (n - d) := by
  change (closedIntegration I n).app (op ⦋0⦌)
    ((closedPullback E.map GT GP n).app (op ⦋0⦌) (zeroForm GT n)) = _
  rw [closedPullback_zero, closedIntegration_zero]

end MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
