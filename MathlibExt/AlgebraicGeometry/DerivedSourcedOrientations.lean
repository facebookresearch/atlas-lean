/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration

/-!
# Fully sourced compactness and orientation models

Every affine base change uses an actual full enriched coefficient
realization and Cech comparison, including positive DG Hom. The
compactness and orientation criteria are evaluated on these same
source models. A raw categorical enhancement is insufficient evidence
for a source-linear RΓ assertion.

The scalar family is chosen together with all these source realizations.
No construction field asserts compactness or nondegeneracy.
Reference: PTVV arXiv:1111.3209v4, Definitions 2.1–2.4.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
variable {k : Type u} [CommRing k] {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k} {V : NerveLiftModel L}
    {X : Prestack k}

/-- Every A-model is tied to its complete native enriched coefficient realization. -/
structure SourcedFamilyModel (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (R : RawModuleRealization M) (Q : AlgebraReplacementFunctor k)
    (L : CochainLiftModel k) (V : NerveLiftModel L) (X : Prestack k) where
  model : FamilyModel M U Q L V X
  gamma : ∀ A : SAlg k, GammaCechData L (model.model A)
  source : ∀ A : SAlg k, SourcedCoefficientImageModel
    (gamma A).category R (model.model A) (gamma A).source (gamma A).unit

/-- The absolute source and all affine models are chosen in the same scalar family. -/
structure SourcedScalarFamily (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (R : RawModuleRealization M) (Q : AlgebraReplacementFunctor k)
    (L : CochainLiftModel k) (V : NerveLiftModel L) (X : Prestack k) where
  family : SourcedFamilyModel M U R Q L V X
  absolute : QCohEnhancement M U X
  scalar : ScalarGlobalModels family.model absolute
  gamma : GammaCechData L absolute
  source : SourcedCoefficientImageModel gamma.category R absolute gamma.source gamma.unit

/-- O-compactness is tested on the complete sourced family, for every A and perfect E. -/
def IsSourcedOCompact {R : RawModuleRealization M}
    (B : SourcedFamilyModel M U R Q L V X) : Prop := IsOCompact B.model

/-- The source orientation test uses the same actual all-A duality, trace and RΓ models, including
the scalar base-change condition of `IsOOrientation`. -/
def IsSourcedOOrientation {R : RawModuleRealization M}
    (B : SourcedScalarFamily M U R Q L V X) {d : ℤ}
    (T : TraceSystem B.family.model B.absolute B.scalar d)
    (C : OrientationContext B.family.model B.absolute) : Prop :=
  IsOOrientation B.family.model B.absolute B.scalar T C

end MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
