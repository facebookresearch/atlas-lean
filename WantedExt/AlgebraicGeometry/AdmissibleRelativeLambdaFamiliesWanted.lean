/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoarseHodgeScaling

/-!
# Normalized admissible relative lambda-family and descent targets

Simpson, alg-geom/9604005v1, Theorem 2.3, Proposition 4.1 (printed p18),
section 4 (p19) and Theorem 9.1 (p39).
The actual section-normalized pullbacks, invariant-subsheaf lambda stability,
native unit/absolute fibres, Betti Chern tests, local finite type presentations,
family isoclasses and affine filtered-colimit functor are fixed in MathlibExt.

All-base admissibility is local finite type descent with full actual family
isomorphisms. Complex-point tests are restricted to those finite type bases.
The last target preserves actual filtered colimits of the fixed affine
family functor. Full all-field l-adic Chern realization is not a prerequisite.
Native invariant lambda stability is retained at nonzero parameters.
Characteristic-class functoriality is an explicit shared source dependency.
Representability, GIT quotient, zero/one fibres, scaling descent and both
framed/coarse etale local products are direct construction targets below.
The quotient universality ranges over arbitrary base changes to its actual
target scheme. Positive rank is retained; dimension zero is included.
No nonabelian Hodge conclusion is assumed.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdmissibleRelativeLambdaFamiliesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaPullbackSystems RelativeDeRhamDifferential
open AdmissibleRelativeLambdaFamilies FramedLambdaFamilyFunctor
open ProjectiveLineSystems PolarizedHiggsStability BettiCharacteristicClasses
open RationalChernZeroHiggsBundles LambdaZeroHiggsComparison
open GeneralLinearFrameSchemes HodgeModuliSchemes FixedParameterLambdaModuli CoarseHodgeScaling

def_wanted framed_pullback_system (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) :
    PullbackSystem X x n

theorem_wanted framed_pullback_coherence (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ)
    (P : PullbackSystem X x n) : PullbackCoherence X x n P

def_wanted unit_fibre_comparison (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ)
    (P : PullbackSystem X x n) : UnitFibreComparison X x n P

def_wanted fibre_tests (X : ComplexScheme) [IsComplexVariety X]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (V : UnitFibreComparison X x n P) : FibreTests X x n P V d H

theorem_wanted zero_semistability (X : ComplexScheme) [IsComplexVariety X]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left]
      [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (_dimension : 0 < d) (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (N : HilbertNumerics X H d)
    (D : Differential X.hom) (C : AbsoluteFormsComparison X)
    (E : LambdaConnectionStability.CoherentConnection X.hom 0 D) :
    LambdaConnectionStability.IsSemistable N E ↔
      PolarizedHiggsStability.IsSemistable N (LambdaConnectionStability.zeroCoherent C E)

theorem_wanted nonzero_semistability (X : ComplexScheme) [IsComplexVariety X]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left]
      [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (N : HilbertNumerics X H d) (D : Differential X.hom)
    (lambda : Γ(Spec (CommRingCat.of ℂ), ⊤)) (_nonzero : lambda ≠ 0)
    (E : LambdaConnectionStability.CoherentConnection X.hom lambda D) (_rank : 0 <
      E.connection.rank) :
    LambdaConnectionStability.IsSemistable N E

theorem_wanted nonzero_rational_chern_zero
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q) (X : ComplexScheme) [IsComplexVariety X]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (A : Differential X.hom) (lambda : Γ(Spec (CommRingCat.of ℂ), ⊤)) (_nonzero : lambda ≠ 0)
    (E : LambdaConnectionStability.CoherentConnection X.hom lambda A)
    (G : ChernGeometry X d E.connection.rank E.connection.object) :
    AllRationalChernZero D Q T.toProjectiveBundleTheory G

theorem_wanted finite_type_admissibility
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q) (S : ComplexScheme)
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (E : Family X x S (P.differential S) n) :
    IsAdmissible X x n P V d H D Q T.toProjectiveBundleTheory F E ↔
      FiniteTypeAdmissible X x n P V d H D Q T.toProjectiveBundleTheory F E

theorem_wanted admissible_reindexing
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q) :
    ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F

theorem_wanted affine_limit_descent
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F) :
    LimitDescent X x n P V d H D Q T.toProjectiveBundleTheory F RP PC


/-- Native GL1 units and scalar action, fixed by actual matrix coordinates. -/
def_wanted scalingParameterTheory [FrameTheory 1] : ScalingParameterTheory

/-- Frame change and unit scaling preserve the fixed admissible families. -/
theorem_wanted actionAdmissibility
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q) :
    ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F

/-- The rank-n polynomial comes from the actual zero/one fibre cohomology. -/
theorem_wanted admissibleRankHilbertPolynomial
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (hO : NumericalCompactifiedJacobians.IsFiniteTypeQuasicoherent
      (CoherentCurveLinearSeries.structureModule (unitProduct X).left))
    (S : ComplexScheme) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (E : Family X x S (P.differential S) n)
    (admissible : FiniteTypeAdmissible X x n P V d H D Q T.toProjectiveBundleTheory F E) :
    ∀ t : scalarBase ⟶ S,
      HasRankHilbertPolynomial X x n P V d H F hO (P.pull X x n t E)

/-- Simpson Proposition 4.1: the actual framed functor, actions and GIT line. -/
def_wanted hodgeRepresentation
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n] :
    HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP

/-- The actual quotient is universal over its target and over the parameter line. -/
def_wanted hodgeQuotient
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP) :
    HodgeQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R

/-- Represent the independently defined constant-parameter family functor. -/
def_wanted fixedRepresentation
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (lambda : ℂ) :
    FixedRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP lambda

/-- The fixed family quotient retains arbitrary target-base-change universality. -/
def_wanted fixedQuotient
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (lambda : ℂ) (R : FixedRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP
      lambda) :
    FixedQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R

/-- At zero, the actual relative operator becomes the integrable Higgs morphism. -/
def_wanted zeroHiggsRealization
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (S : ComplexScheme) (E : FixedFamily X x n P V d H D Q T.toProjectiveBundleTheory F 0 S) :
    ZeroHiggsRealization X x n P V d H D Q T.toProjectiveBundleTheory F E

/-- At one, both actual connection operators and the frame specialize literally. -/
def_wanted oneFlatRealization
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (S : ComplexScheme) (E : FixedFamily X x n P V d H D Q T.toProjectiveBundleTheory F 1 S) :
    OneFlatRealization X x n P V d H D Q T.toProjectiveBundleTheory F E

/-- Both fibre isomorphisms preserve the actual family classes and quotient square. -/
def_wanted hodgeFibreIdentification
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (lambda : ℂ) (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP)
    (C : HodgeQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R)
    (Rfix : FixedRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP lambda)
    (Cfix : FixedQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP Rfix) :
    FibreIdentification X x n P V d H D Q T.toProjectiveBundleTheory F RP AP lambda R C Rfix Cfix

/-- Descend the literal scalar multiplication of the actual family operators. -/
def_wanted coarseScalingDescent
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP) (C :
      HodgeQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R) :
    ScalingDescent X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R C

/-- The nonzero-fibre map is scaling by lambda inverse, in both directions. -/
def_wanted nonzeroFibreScaling
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP) (C :
      HodgeQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R)
    (S : ScalingDescent X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R C) (lambda : ℂ)
      (nonzero : lambda ≠ 0) :
    NonzeroFibreScaling X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R C S lambda nonzero

/-- Theorem 9.1 for the actual framed Hodge representation scheme. -/
def_wanted framedEtaleLocalProduct
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP) (y :
      scalarBase ⟶ R.scheme) :
    EtaleLocalProduct R.scheme R.parameter y

/-- Theorem 9.1 for the actual universal coarse Hodge quotient scheme. -/
def_wanted coarseEtaleLocalProduct
    (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] [IsNoetherian X.left] [IsIntegral X.left]
    (_projective : ProjectiveSpace.IsProjective X)
    (x : scalarBase ⟶ X) (n : ℕ) (_rank : 0 < n)
    (H : LineBundle X.left) (_ample : IsAmpleLine H)
    (P : PullbackSystem X x n) (PC : PullbackCoherence X x n P)
    (V : UnitFibreComparison X x n P)
    [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
    (F : FibreTests X x n P V d H)
    (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
    (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
      (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
    (T : CharacteristicClassTheory D Q)
    (RP : ReindexingProofs X x n P V d H D Q T.toProjectiveBundleTheory F)
    (AP : ActionAdmissibility X x n P V d H D Q T.toProjectiveBundleTheory F)
    [FrameTheory 1] [ScalingParameterTheory] [FrameTheory n]
    (R : HodgeRepresentation X x n P V d H D Q T.toProjectiveBundleTheory F RP AP) (C :
      HodgeQuotient X x n P V d H D Q T.toProjectiveBundleTheory F RP AP R)
    (y : scalarBase ⟶ C.scheme) :
    EtaleLocalProduct C.scheme C.parameter y

end WantedExt.AlgebraicGeometry.AdmissibleRelativeLambdaFamiliesWanted
