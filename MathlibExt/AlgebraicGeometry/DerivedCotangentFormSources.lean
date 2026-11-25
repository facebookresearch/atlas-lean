/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces

/-!
# Entry data for native cotangents and closed-form spaces

The package keeps the actual QCoh cotangent, perfect dual, exterior,
full universal affine cone, native NC complexes and computed comparison.
Its contraction is one source-compatible cochain map, so both vertices
and paths use the same normalized coefficient calculation. The fields
record shared source choices and proofs; no shifted symplectic or
Lagrangian conclusion is a package field.

Source: PTVV arXiv:1111.3209v4, Sections 1.2 and 2.2. Imported source
pins, licenses and native operator notices are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
open MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k}

/-- Shared native source data expose actual objects and operators, with proof availability separate. -/
structure CotangentFormSources (X : Prestack k) where
  global : QCohEnhancement M U X
  context : CotangentContext R global
  monoidal : CoherentMonoidalEnhancement global
  exterior : ExteriorSquare monoidal context.cotangent.object
  affine : UniversalExteriorFamilies D L X global context monoidal exterior
  cone : CoherentExteriorCone affine
  forms : GlobalNCModel D 2 NC X
  parameterForms : GlobalNCModel D 2 NC (affineParameterPrestack Q X)
  [weightLimits : PreservesLimit parameterForms.ordinary.diagram (coefficientWeightFunctor k)]
  [parameterComparison : QuasiIso (coefficientWeightPullback (affineParameterPoint Q X) forms parameterForms)]
  exteriorComparison : GlobalExteriorRepresentative cone forms parameterForms
  [exteriorQuasiIso : QuasiIso exteriorComparison.map]
  tangent : PerfectDual monoidal.monoidal context.cotangent.object
  contraction : NCContractionSource exteriorComparison tangent

/-- The source's actual NC closed forms, with every closing coefficient retained. -/
abbrev SourceClosedForm {X : Prestack k} (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) := ClosedForm F.forms n

/-- Theta is the same source cochain/DK vertex coefficient. -/
def sourceTheta {X : Prestack k} (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) (ω : SourceClosedForm F n) :
    DGHom (LargeScalar k) n F.tangent.object F.context.cotangent.object := by
  letI := F.weightLimits
  letI := F.parameterComparison
  letI := F.exteriorQuasiIso
  exact DerivedNativeContractionSpaces.theta F.exteriorComparison F.tangent F.contraction n ω

/-- Its native closedness is proved from the normalized source coefficient. -/
theorem sourceTheta_closed {X : Prestack k}
    (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) (ω : SourceClosedForm F n) : dgDifferential (LargeScalar k) n (sourceTheta F n ω) = 0 := by
  have := F.weightLimits
  have := F.parameterComparison
  have := F.exteriorQuasiIso
  exact DerivedNativeContractionSpaces.theta_closed F.exteriorComparison F.tangent F.contraction n ω

/-- The actual isotropic path gives the signed degree-(n-1) coefficient of that same source map. -/
def sourceIsotropicHomotopy {X : Prestack k}
    (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) (ω : SourceClosedForm F n) (h : IsotropicPath F.forms n ω) :
    DGHom (LargeScalar k) (n - 1) F.tangent.object F.context.cotangent.object := by
  letI := F.weightLimits
  letI := F.parameterComparison
  letI := F.exteriorQuasiIso
  exact DerivedNativeContractionSpaces.isotropicHomotopy F.exteriorComparison F.tangent F.contraction n ω h

/-- The isotropic boundary is the same actual source Theta. -/
theorem sourceIsotropicHomotopy_boundary {X : Prestack k}
    (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) (ω : SourceClosedForm F n) (h : IsotropicPath F.forms n ω) :
    ((dgHomComplex (LargeScalar k) F.tangent.object F.context.cotangent.object).d (n - 1) n).hom
      (sourceIsotropicHomotopy F n ω h) = sourceTheta F n ω := by
  have := F.weightLimits
  have := F.parameterComparison
  have := F.exteriorQuasiIso
  exact DerivedNativeContractionSpaces.isotropicHomotopy_boundary
    F.exteriorComparison F.tangent F.contraction n ω h

/-- The same actual cochain contraction, exposed without repeating the source instance binders. -/
def sourceContraction {X : Prestack k}
    (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X) :
    (ncComplex F.forms)⟦-2⟧ ⟶ homGlobal F.tangent.object F.context.cotangent.object := by
  letI := F.weightLimits
  letI := F.parameterComparison
  letI := F.exteriorQuasiIso
  exact F.contraction.map

/-- Nondegeneracy is a property of the actual source Theta, not an input model flag. -/
def IsSourceSymplectic {X : Prestack k}
    (F : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X)
    (n : ℤ) (ω : SourceClosedForm F n) : Prop :=
  IsShiftedEquivalence F.context.cotangent.object F.tangent.object n (sourceTheta F n ω)
    (sourceTheta_closed F n ω)

end MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
