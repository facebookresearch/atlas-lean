/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedSourceMappingCoefficientMaps
public import MathlibExt.AlgebraicGeometry.DerivedSourceMappingIntegration
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

/-!
# Source requests for mapping evaluation, coefficients and transgression

Map(X,F) has a separate native derived-Artin/LFP witness. O-compactness
of arbitrary X is not asserted to imply representability. Factories
construct actual all-degree evaluation/pullback/right-adjoint sources,
and actual normalized affine RΓ module mates. The mapping tangent is
the independently corepresented cotangent dual.

The integral factory returns a representative of the computed original
global relative de Rham/NC/trace class. The nondegeneracy conclusion
concerns the literal evaluation-pullback/integral form of degree n-d.
All-A source orientation is a hypothesis; no output equivalence or
transgressed symplectic structure is a constructor hypothesis.

Source: PTVV arXiv:1111.3209v4, Definitions 2.1--2.4 and Theorem 2.5,
pp.30--35; HAG II arXiv:math/0404373v7, Section 1.4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DerivedSourceMappingWanted

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents
open MathlibExt.AlgebraicGeometry.DerivedSourceMappingCoefficientMaps
open MathlibExt.AlgebraicGeometry.DerivedSourceMappingIntegration
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k] [IsNoetherianRing k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k} {V : NerveLiftModel L}

/-- Choose source evaluation, independent mapping cotangent and all-degree native RΓ adjunctions.
The geometricity and derived LFP of the computed Map are supplied separately. -/
def_wanted native_mapping_tangent_sources (X F : DerivedStack Q) (RF : FibrantReplacement F.functor)
    (E : EvaluationModel Q X.functor F.functor RF)
    (BX : SourcedScalarFamily M U R Q L V X.functor) (compact : IsSourcedOCompact BX.family)
    (gf : IsDerivedArtin F) (lf : IsLocallyOfFinitePresentationStack F)
    (Map : DerivedStack Q) (mapping_eq : Map.functor = mappingPrestackFunctor k Q X.functor F.functor RF)
    (gm : IsDerivedArtin Map) (lm : IsLocallyOfFinitePresentationStack Map) :
    MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E

/-- Prove equivalence for the computed evaluation adjoint transpose, independently of its construction. -/
theorem_wanted native_mapping_tangent_comparison_equivalence
    (X F : DerivedStack Q) (RF : FibrantReplacement F.functor)
    (E : EvaluationModel Q X.functor F.functor RF)
    (BX : SourcedScalarFamily M U R Q L V X.functor) (compact : IsSourcedOCompact BX.family)
    (gf : IsDerivedArtin F) (lf : IsLocallyOfFinitePresentationStack F)
    (Map : DerivedStack Q) (mapping_eq : Map.functor = mappingPrestackFunctor k Q X.functor F.functor RF)
    (gm : IsDerivedArtin Map) (lm : IsLocallyOfFinitePresentationStack Map)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E) :
    IsShiftedEquivalence (evaluationGamma E B) B.mapping.tangent.object 0
      (mappingTangentComparison E B) (mappingTangentComparison_closed E B)

/-- Construct the actual complete affine pullback square, its adjunctions and coefficient-unit normalization. -/
def_wanted native_affine_mapping_gamma_sources
    {X F : Prestack k} {RF : FibrantReplacement F} (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : SourcedScalarFamily M U R Q L V X) (compact : IsSourcedOCompact BX.family)
    (A : SAlg k) (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF) :
    AffineMappingGammaSources E B BX.family.model A f

/-- Lift the already computed projection/counit mate to its actual native A-linear module map. -/
def_wanted native_affine_mapping_gamma_module_map
    {X F : Prestack k} {RF : FibrantReplacement F} (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : SourcedScalarFamily M U R Q L V X) (compact : IsSourcedOCompact BX.family)
    (A : SAlg k) (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF)
    (C : AffineMappingGammaSources E B BX.family.model A f) :
    AffineGammaModuleMap E B BX.family.model A f C

/-- The actual coefficient mate computes RΓ_X_A(f*T_F), with every A-action retained. -/
theorem_wanted native_affine_mapping_gamma_quasiIso
    {X F : Prestack k} {RF : FibrantReplacement F} (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : SourcedScalarFamily M U R Q L V X) (compact : IsSourcedOCompact BX.family)
    (A : SAlg k) (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF)
    (C : AffineMappingGammaSources E B BX.family.model A f)
    (W : AffineGammaModuleMap E B BX.family.model A f C) :
    ∀ c, QuasiIso (moduleComponent W.map c)

/-- Choose the native NC/relative de Rham integral representative of the actual trace class. -/
def_wanted native_mapping_integration_sources
    {X F : Prestack k} {RF : FibrantReplacement F} (E : EvaluationModel Q X F RF)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (BX : SourcedScalarFamily M U R Q L V X) (compact : IsSourcedOCompact BX.family)
    (d : ℤ) (trace : TraceSystem BX.family.model BX.absolute BX.scalar d)
    (C : OrientationContext BX.family.model BX.absolute)
    (orientation : IsSourcedOOrientation BX trace C) : MappingIntegrationSources E B BX trace

/-- PTVV nondegeneracy for the literal evaluation/integration form, degree n-d and trace degree -d. -/
theorem_wanted native_mapping_transgression_nondegenerate
    (X F : DerivedStack Q) (RF : FibrantReplacement F.functor)
    (E : EvaluationModel Q X.functor F.functor RF)
    (BX : SourcedScalarFamily M U R Q L V X.functor) (compact : IsSourcedOCompact BX.family)
    (gf : IsDerivedArtin F) (lf : IsLocallyOfFinitePresentationStack F)
    (Map : DerivedStack Q) (mapping_eq : Map.functor = mappingPrestackFunctor k Q X.functor F.functor RF)
    (gm : IsDerivedArtin Map) (lm : IsLocallyOfFinitePresentationStack Map)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (d : ℤ) (trace : TraceSystem BX.family.model BX.absolute BX.scalar d)
    (C : OrientationContext BX.family.model BX.absolute) (orientation : IsSourcedOOrientation BX trace C)
    (I : MappingIntegrationSources E B BX trace)
    (n : ℤ) (ω : SourceClosedForm B.target n) (symplectic : IsSourceSymplectic B.target n ω) :
    IsSourceSymplectic B.mapping (n - d) (sourceMappingTransgressForm E B BX trace I n ω)

end WantedExt.AlgebraicGeometry.DerivedSourceMappingWanted
