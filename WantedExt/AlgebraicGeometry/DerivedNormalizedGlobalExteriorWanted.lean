/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

/-!
# Source construction requests for the computed global exterior comparison

The factories construct native modules/maps and whole coherent diagrams.
RΓ first enters the actual injective exterior coefficient diagram. The
raw augmentation is inverted only in the localization of entire diagrams.
The exterior map is a full DG coefficient-section map on a projective
source, followed by the original QQ/QA/derived-scalar span. The final
cone enters the injective weight target and has that whole diagram class.
The unresolved comparison proof concerns the computed RΓ(exterior-square
L_F) to DR(F)(2)[-2] map. Neither that map nor its equivalence is an input
endpoint. All QA polynomial/simplex forms, actions, balanced quotient,
gauge parameters, units and source cotangent transposes remain specified.

Sources: PTVV arXiv:1111.3209v4, Section 1.1, Proposition 1.14 and
Lemma 1.15; HAG II arXiv:math/0404373v7, Sections 1.3.7 and 1.4.1.
These direct Batteries ProofWanted requests are interface entry hooks;
proving provider theory is not a prerequisite for paper-specific tasks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
open MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons
open MathlibExt.AlgebraicGeometry.DerivedResolvedExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u

/-- Resolve the complete affine mapping/simplex algebra diagram with its original QQ to QA square. -/
def_wanted native_whole_polynomial_algebra_diagram (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (X : DerivedStack Q) :
    PolynomialAlgebraDiagram Q (affineParameterPrestack Q X.functor)

/-- Construct the actual polynomial cotangent, balanced exterior module and native generator shuffle. -/
def_wanted native_polynomial_exterior_module (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (A : SAlg k) (cofibrant : IsAlgebraCofibrant A)
    (F : MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels.SimplicialDRModel A) :
    PolynomialExteriorModule N A F

/-- Assemble whole QQ exterior-module, actual extension-unit and original QQ to QA form diagrams. -/
def_wanted native_whole_polynomial_exterior_span (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (D : AffineDRSystem Q) (X : DerivedStack Q)
    (P : PolynomialAlgebraDiagram Q (affineParameterPrestack Q X.functor)) :
    PolynomialExteriorSpan (N := N) D P

/-- The actual extension unit is compared independently of eta or any global endpoint. -/
theorem_wanted native_polynomial_exterior_scalar_unit_quasiIso (k : Type u) [CommRing k]
    [Algebra ℚ k] (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (D : AffineDRSystem Q) (X : DerivedStack Q)
    (P : PolynomialAlgebraDiagram Q (affineParameterPrestack Q X.functor))
    (S : PolynomialExteriorSpan (N := N) D P) : ∀ j, QuasiIso (S.scalarUnit.app j)

/-- The exact QQ to QA balanced generator comparison is a source affine theorem. -/
theorem_wanted native_polynomial_exterior_toQA_quasiIso (k : Type u) [CommRing k]
    [Algebra ℚ k] (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (D : AffineDRSystem Q) (X : DerivedStack Q)
    (P : PolynomialAlgebraDiagram Q (affineParameterPrestack Q X.functor))
    (S : PolynomialExteriorSpan (N := N) D P) : ∀ j, QuasiIso ((polynomialToQA S).app j)

/-- Construct the actual QA cotangent module with its fixed native Moore coefficients and scalar shuffle. -/
def_wanted resolved_native_cotangent_forms (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (D : AffineDRSystem Q) (A : SAlg k) : ResolvedCotangentModule N D A

/-- Assemble the literal signed polynomial/simplex wedge coefficients into their native cochain map. -/
def_wanted normalized_native_form_wedge (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (A : SAlg k) :
    NormalizedFormWedge (D.forms A)

/-- Split the actual native rational skew projector of the balanced derived module tensor. -/
def_wanted native_module_exterior_square (k : Type u) [CommRing k] [Algebra ℚ k]
    (C : DGCat k) (o : C) (hC : IsCommutativeCoefficient C o)
    (T : DerivedTensorModel C o) (unit : DGDerivedModules k C)
    (unit_eq : unit.obj = regularModule C o) (B : CoherenceModel C o T unit unit_eq)
    (P : DGDerivedModules k C) : ModuleExteriorSquare C o T unit unit_eq B P

/-- Construct the QA exterior comparison fixed on the whole native balanced quotient. -/
def_wanted resolved_native_exterior_form_comparison (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (D : AffineDRSystem Q)
    (A : SAlg k) (P : ResolvedCotangentModule N D A)
    (T : DerivedTensorModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (unit : DGDerivedModules k (coefficientCategory N (Q.functor.obj A)))
    (unit_eq : unit.obj = regularModule (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (B : CoherenceModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit T unit unit_eq)
    (E : ModuleExteriorSquare (coefficientCategory N (Q.functor.obj A)) PUnit.unit T unit unit_eq B P.module)
    (W : NormalizedFormWedge (D.forms A)) : ResolvedExteriorFormComparison N D A P T unit unit_eq B E W

/-- Prove the actual generator-normalized QA exterior comparison, separately from its constructor. -/
theorem_wanted resolved_native_exterior_form_comparison_quasiIso
    (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (D : AffineDRSystem Q)
    (A : SAlg k) (P : ResolvedCotangentModule N D A)
    (T : DerivedTensorModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (unit : DGDerivedModules k (coefficientCategory N (Q.functor.obj A)))
    (unit_eq : unit.obj = regularModule (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (B : CoherenceModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit T unit unit_eq)
    (E : ModuleExteriorSquare (coefficientCategory N (Q.functor.obj A)) PUnit.unit T unit unit_eq B P.module)
    (W : NormalizedFormWedge (D.forms A)) (C : ResolvedExteriorFormComparison N D A P T unit unit_eq B E W) :
    QuasiIso C.map

/-- Choose coupled source models, the full DG splitting transpose and the entire localized injective cone. -/
def_wanted coherent_native_global_exterior_sources (k : Type u) [CommRing k] [Algebra ℚ k]
    [IsNoetherianRing k] (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (M : AffineModuleFibration N S)
    (U : RegularUnitSystem M) (R : RawModuleRealization M) (L : CochainLiftModel k)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X) (lfp : IsLocallyOfFinitePresentationStack X) :
    Σ G : QCohEnhancement M U X.functor, Σ C : CotangentContext R G,
      Σ H : CoherentMonoidalEnhancement G, Σ E : ExteriorSquare H C.cotangent.object,
        Σ B : UniversalExteriorFamilies D L X.functor G C H E, CoherentExteriorCone B

/-- The actual augmentation evaluator is a source affine Yoneda equivalence on every full mapping space. -/
theorem_wanted native_affine_parameter_evaluation_weak (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (X : DerivedStack Q) :
    ∀ A : SAlg k, MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.WeakEquivalence
      ((affineParameterPoint Q X.functor).app A)

/-- Prove the actual complete weight restriction along that evaluator, not an independent global form isomorphism. -/
theorem_wanted native_parameter_weight_pullback_quasiIso (k : Type u) [CommRing k] [Algebra ℚ k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (NC : NegativeCyclicDiagram D.functor (2 : ℤ)) (X : DerivedStack Q)
    (FF : GlobalNCModel D 2 NC X.functor)
    (FP : GlobalNCModel D 2 NC (affineParameterPrestack Q X.functor)) :
    QuasiIso (coefficientWeightPullback (affineParameterPoint Q X.functor) FF FP)

/-- Construct a native cochain representative of the already computed injective global exterior map. -/
def_wanted computed_global_exterior_representative (k : Type u) [CommRing k] [Algebra ℚ k]
    [IsNoetherianRing k] (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (NC : NegativeCyclicDiagram D.functor (2 : ℤ))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (M : AffineModuleFibration N S)
    (U : RegularUnitSystem M) (R : RawModuleRealization M) (L : CochainLiftModel k)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X) (lfp : IsLocallyOfFinitePresentationStack X)
    (G : QCohEnhancement M U X.functor) (CY : CotangentContext R G)
    (H : CoherentMonoidalEnhancement G) (E : ExteriorSquare H CY.cotangent.object)
    (B : UniversalExteriorFamilies D L X.functor G CY H E) (C : CoherentExteriorCone B)
    (FF : GlobalNCModel D 2 NC X.functor)
    (FP : GlobalNCModel D 2 NC (affineParameterPrestack Q X.functor))
    [PreservesLimit FP.ordinary.diagram (coefficientWeightFunctor k)]
    [QuasiIso (coefficientWeightPullback (affineParameterPoint Q X.functor) FF FP)] :
    GlobalExteriorRepresentative C FF FP

/-- Source nondegeneracy of eta is requested for that same computed map, independently of its construction. -/
theorem_wanted computed_global_exterior_quasiIso (k : Type u) [CommRing k] [Algebra ℚ k]
    [IsNoetherianRing k] (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (NC : NegativeCyclicDiagram D.functor (2 : ℤ))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (M : AffineModuleFibration N S)
    (U : RegularUnitSystem M) (R : RawModuleRealization M) (L : CochainLiftModel k)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X) (lfp : IsLocallyOfFinitePresentationStack X)
    (G : QCohEnhancement M U X.functor) (CY : CotangentContext R G)
    (H : CoherentMonoidalEnhancement G) (E : ExteriorSquare H CY.cotangent.object)
    (B : UniversalExteriorFamilies D L X.functor G CY H E) (C : CoherentExteriorCone B)
    (FF : GlobalNCModel D 2 NC X.functor)
    (FP : GlobalNCModel D 2 NC (affineParameterPrestack Q X.functor))
    [PreservesLimit FP.ordinary.diagram (coefficientWeightFunctor k)]
    [QuasiIso (coefficientWeightPullback (affineParameterPoint Q X.functor) FF FP)]
    (Eη : GlobalExteriorRepresentative C FF FP) : QuasiIso Eη.map

end WantedExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorWanted
