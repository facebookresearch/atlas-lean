/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham

/-!
# Source normalized global NC integration class

The relative class is the computed global κ. Both global NC bridges
are actual limit maps through the full source augmentation squares.
Integration then uses the canonical finite-coefficient NC comparison,
the actual RΓ scalar trace, and the native unit/shift comparison.

This supplies the concrete derived morphism which a cochain integration
representative must realize before literal evaluation transgression.
Generic realization constructors and source comparison proofs are
requested separately.

Reference: PTVV arXiv:1111.3209v4, Definitions 2.3–2.4, Theorem 2.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
open MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {L : CochainLiftModel k} {T : MixedLiftModel L}
    {p : ℕ} {N : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}

/-- One complete NC comparison packet retains every native source coefficient and square. -/
structure GlobalNCData (G : GlobalMixedModel D T X) (F : GlobalNCModel D p N X) where
  affine : LiftedNCDiagram D T p N
  replacement : ReplacementNCDiagram G affine
  limit : MixedLimitNC replacement
  lift : GlobalNCLift replacement F

/-- The comparison is the literal full limit lift followed by the native NC term iso. -/
def GlobalNCData.comparison {G : GlobalMixedModel D T X} {F : GlobalNCModel D p N X}
    (A : GlobalNCData G F) (C : NCCategoryModel (LargeScalar k) (p : ℤ)) :
    (globalToCoefficients k).obj (ncComplex F) ⟶ C.diagram.complex.obj G.mixed :=
  globalNCToFunctor A.limit A.lift C

variable {SAlgN : ShuffleAlgebraFunctor k} {S : AffineScalarSystem SAlgN}
    {M : AffineModuleFibration SAlgN S} {U : RegularUnitSystem M} {V : NerveLiftModel L}
    {F : Prestack k} (B : FamilyModel M U Q L V X) (GX : QCohEnhancement M U X)
    (SC : ScalarGlobalModels B GX) (C : GammaCechData L GX)

/-- Global integration is computed from the actual normalized κ class and RΓ trace. -/
def globalIntegrationClass {R : ProductReplacementSystem Q} {SL : StrongCochainLift L}
    {G : GlobalMixedModel D T F} {GP : GlobalMixedModel D T (F ⊗ X)}
    {P : PureTensorModel G.mixed (gammaCoefficients B GX SC)}
    (A : GlobalRelativeModel B GX SC C R SL G GP P)
    (projectionWeak : ∀ w : ℤ, QuasiIso (A.projection.map.map w))
    (W : NCCategoryModel (LargeScalar k) (p : ℤ))
    (K : Comparison P (p : ℤ) (W.diagram.toModel G.mixed) (W.diagram.toModel P.mixed))
    [IsIso (DerivedCategory.Q.map K.map)] {d : ℤ} (η : TraceSystem B GX SC d)
    (shift : UnitTensorModel (W.diagram.complex.obj G.mixed) (-d))
    {FP : GlobalNCModel D p N (F ⊗ X)} {FF : GlobalNCModel D p N F}
    (NP : GlobalNCData GP FP) (NF : GlobalNCData G FF)
    [IsIso (DerivedCategory.Q.map
      ((shiftFunctor (Cochains (LargeScalar k)) (-d)).map (NF.comparison W)))] :
    DerivedCategory.Q.obj ((globalToCoefficients k).obj (ncComplex FP)) ⟶
      DerivedCategory.Q.obj (((globalToCoefficients k).obj (ncComplex FF))⟦-d⟧) :=
  DerivedCategory.Q.map (NP.comparison W) ≫
    integrateClass W P (globalKappa B GX SC C A projectionWeak) K
      (gammaTrace B GX SC η) shift ≫
    inv (DerivedCategory.Q.map
      ((shiftFunctor (Cochains (LargeScalar k)) (-d)).map (NF.comparison W)))

end MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
