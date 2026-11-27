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

/-- Change of frame and scaling preserve admissibility. Let $X$ be an integral, Noetherian, proper
and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an ample line
bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$ relative
λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the given
pullback system with its coherence, unit-fibre comparison and fibre tests, and the given dualizing
complexes, proper pullbacks and characteristic class theory. Then for every complex scheme $S$ and
every admissible family $E$ over $S$, changing the frame of $E$ by an automorphism of
$\mathcal{O}_S^n$, or scaling $E$ by a unit of $\Gamma(S, \mathcal{O}_S)$, gives an admissible
family (`ActionAdmissibility`). -/
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

/-- Admissible families have the rank-$n$ Hilbert polynomial. Let $X$ be an integral, Noetherian,
proper and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an
ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$
relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the
given pullback system with its coherence, unit-fibre comparison and fibre tests, and the given
dualizing complexes, proper pullbacks and characteristic class theory. Assume the structure sheaf of
$X \times \operatorname{Spec} \mathbb{C}$ quasi-coherent of finite type, and let $E$ be a family
over a complex scheme $S$ of finite type that is admissible on finite type bases
(`FiniteTypeAdmissible`). Then at every complex point $t$ of $S$, the underlying sheaf of the fibre
of $E$ at $t$ has Hilbert polynomial, for the polarization of the fibre tests, equal to $n$ times
that of the structure sheaf (`HasRankHilbertPolynomial`). -/
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

/-- Simpson, Proposition 4.1: the framed Hodge moduli space. Let $X$ be an integral, Noetherian,
proper and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an
ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$
relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the
given pullback system with its coherence, unit-fibre comparison and fibre tests, and the given
dualizing complexes, proper pullbacks and characteristic class theory. Assume admissibility stable
under reindexing and under change of frame and scaling (`ReindexingProofs`, `ActionAdmissibility`),
and fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$ and scaling action of
$\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`). Then there is a complex
scheme $R$ of finite type with a map $R \to \mathbb{A}^1$ such that maps $S \to R$ correspond,
naturally in $S$, to isomorphism classes of admissible families over $S$, the map to $\mathbb{A}^1$
recording the parameter λ. Moreover $R$ carries a $\mathrm{GL}_n$-action realizing change of frame
and preserving the parameter, a $\mathrm{GL}_1$-action realizing scaling of families and compatible
with multiplication on $\mathbb{A}^1$, and an ample $\mathrm{GL}_n$-linearized line bundle for which
every field-valued point is semistable (`HodgeRepresentation`). -/
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

/-- The coarse Hodge moduli space, as a universal categorical quotient. Let $X$ be an integral,
Noetherian, proper and projective complex variety, smooth of dimension $d$, with a complex point $x$
and an ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed
rank-$n$ relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken
for the given pullback system with its coherence, unit-fibre comparison and fibre tests, and the
given dualizing complexes, proper pullbacks and characteristic class theory. Assume admissibility
stable under reindexing and under change of frame and scaling (`ReindexingProofs`,
`ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$
and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`).
Given a framed Hodge moduli space $R \to \mathbb{A}^1$ for these data (`HodgeRepresentation`), there
is a complex scheme $M$ of finite type with a map to $\mathbb{A}^1$ and a $\mathrm{GL}_n$-invariant
map $R \to M$ over $\mathbb{A}^1$ that remains a categorical quotient after every base change along
a map to $M$, and after every base change along a map to $\mathbb{A}^1$ (`HodgeQuotient`). -/
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

/-- The moduli space at a fixed parameter λ. Let $X$ be an integral, Noetherian, proper and
projective complex variety, smooth of dimension $d$, with a complex point $x$ and an ample line
bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$ relative
λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the given
pullback system with its coherence, unit-fibre comparison and fibre tests, and the given dualizing
complexes, proper pullbacks and characteristic class theory. Assume admissibility stable under
reindexing and under change of frame and scaling (`ReindexingProofs`, `ActionAdmissibility`), and
fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$ and scaling action of
$\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`). Then for every
$\lambda \in \mathbb{C}$, the isomorphism classes of admissible families over $S$ with constant
parameter λ are represented, naturally in $S$, by a complex scheme of finite type with a
$\mathrm{GL}_n$-action realizing change of frame (`FixedRepresentation`). -/
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

/-- The coarse moduli space at a fixed parameter λ. Let $X$ be an integral, Noetherian, proper and
projective complex variety, smooth of dimension $d$, with a complex point $x$ and an ample line
bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$ relative
λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the given
pullback system with its coherence, unit-fibre comparison and fibre tests, and the given dualizing
complexes, proper pullbacks and characteristic class theory. Assume admissibility stable under
reindexing and under change of frame and scaling (`ReindexingProofs`, `ActionAdmissibility`), and
fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$ and scaling action of
$\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`). Given
$\lambda \in \mathbb{C}$ and a complex scheme $R_\lambda$ representing the admissible families with
constant parameter λ (`FixedRepresentation`), there is a complex scheme of finite type with a
categorical quotient map from $R_\lambda$ by the $\mathrm{GL}_n$-action that remains a categorical
quotient after every base change along a map to its target (`FixedQuotient`). -/
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

/-- At λ = 0, an admissible family is a framed Higgs bundle. Let $X$ be an integral, Noetherian,
proper and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an
ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$
relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the
given pullback system with its coherence, unit-fibre comparison and fibre tests, and the given
dualizing complexes, proper pullbacks and characteristic class theory. Then for every complex scheme
$S$ and every admissible family $E$ over $S$ with constant parameter $0$, there are a framed
rank-$n$ vector bundle on $X \times S$ with an integrable relative Higgs field $\theta$ (that is,
$\theta \wedge \theta = 0$) and an isomorphism from the bundle of $E$ to it carrying the operator of
$E$ to $\theta$ and the frame of $E$ to its frame (`ZeroHiggsRealization`). -/
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

/-- At λ = 1, an admissible family is a framed flat connection. Let $X$ be an integral, Noetherian,
proper and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an
ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$
relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the
given pullback system with its coherence, unit-fibre comparison and fibre tests, and the given
dualizing complexes, proper pullbacks and characteristic class theory. Then for every complex scheme
$S$ and every admissible family $E$ over $S$ with constant parameter $1$, there are a framed
rank-$n$ relative λ-connection with parameter $1$, that is, an integrable relative connection
(`FlatFamily`), and an isomorphism from the bundle of $E$ to its bundle carrying both connection
operators of $E$ to its operators and the frame of $E$ to its frame (`OneFlatRealization`). -/
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

/-- The fibres over λ of the Hodge moduli spaces are the fixed-parameter moduli spaces. Let $X$ be
an integral, Noetherian, proper and projective complex variety, smooth of dimension $d$, with a
complex point $x$ and an ample line bundle $H$, and let $n > 0$. Families over a complex scheme $S$
are framed rank-$n$ relative λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`)
is taken for the given pullback system with its coherence, unit-fibre comparison and fibre tests,
and the given dualizing complexes, proper pullbacks and characteristic class theory. Assume
admissibility stable under reindexing and under change of frame and scaling (`ReindexingProofs`,
`ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$
and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`).
Given the framed and coarse Hodge moduli spaces $R \to M$ (`HodgeRepresentation`, `HodgeQuotient`)
and, for $\lambda \in \mathbb{C}$, fixed-parameter spaces $R_\lambda \to M_\lambda$
(`FixedRepresentation`, `FixedQuotient`), there are isomorphisms from the fibre of $R$ over
$\lambda \in \mathbb{A}^1$ to $R_\lambda$ and from the fibre of $M$ over λ to $M_\lambda$ that
identify the family classes represented by maps to the fibre of $R$ with those represented by
$R_\lambda$, and that commute with the quotient maps (`FibreIdentification`). -/
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

/-- Scaling descends to the coarse Hodge moduli space. Let $X$ be an integral, Noetherian, proper
and projective complex variety, smooth of dimension $d$, with a complex point $x$ and an ample line
bundle $H$, and let $n > 0$. Families over a complex scheme $S$ are framed rank-$n$ relative
λ-connections on $X \times S$ over $S$; admissibility (`IsAdmissible`) is taken for the given
pullback system with its coherence, unit-fibre comparison and fibre tests, and the given dualizing
complexes, proper pullbacks and characteristic class theory. Assume admissibility stable under
reindexing and under change of frame and scaling (`ReindexingProofs`, `ActionAdmissibility`), and
fix the given frame structures on $\mathrm{GL}_n$ and $\mathrm{GL}_1$ and scaling action of
$\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`, `ScalingParameterTheory`). Given the framed and
coarse Hodge moduli spaces $R \to M$ (`HodgeRepresentation`, `HodgeQuotient`), there is an action of
$\mathrm{GL}_1$ on $M$ for which the quotient map $R \to M$ is equivariant for the scaling action on
$R$, and the map $M \to \mathbb{A}^1$ is equivariant for multiplication on $\mathbb{A}^1$
(`ScalingDescent`). -/
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

/-- For λ ≠ 0, scaling identifies the fibre over λ of the coarse Hodge moduli space with its fibre
over 1. Let $X$ be an integral, Noetherian, proper and projective complex variety, smooth of
dimension $d$, with a complex point $x$ and an ample line bundle $H$, and let $n > 0$. Families over
a complex scheme $S$ are framed rank-$n$ relative λ-connections on $X \times S$ over $S$;
admissibility (`IsAdmissible`) is taken for the given pullback system with its coherence, unit-fibre
comparison and fibre tests, and the given dualizing complexes, proper pullbacks and characteristic
class theory. Assume admissibility stable under reindexing and under change of frame and scaling
(`ReindexingProofs`, `ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$
and $\mathrm{GL}_1$ and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`,
`ScalingParameterTheory`). Given the framed and coarse Hodge moduli spaces $R \to M$
(`HodgeRepresentation`, `HodgeQuotient`), a descended $\mathrm{GL}_1$-action on $M$
(`ScalingDescent`) and $\lambda \neq 0$, there is an isomorphism from the fibre of $M$ over λ to its
fibre over $1$ that is scaling by $\lambda^{-1}$, with inverse scaling by λ, compatibly with the
inclusions of the fibres into $M$ (`NonzeroFibreScaling`). -/
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

/-- Simpson, Theorem 9.1, for the framed Hodge moduli space: it is étale locally a product with
$\mathbb{A}^1$. Let $X$ be an integral, Noetherian, proper and projective complex variety, smooth of
dimension $d$, with a complex point $x$ and an ample line bundle $H$, and let $n > 0$. Families over
a complex scheme $S$ are framed rank-$n$ relative λ-connections on $X \times S$ over $S$;
admissibility (`IsAdmissible`) is taken for the given pullback system with its coherence, unit-fibre
comparison and fibre tests, and the given dualizing complexes, proper pullbacks and characteristic
class theory. Assume admissibility stable under reindexing and under change of frame and scaling
(`ReindexingProofs`, `ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$
and $\mathrm{GL}_1$ and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`,
`ScalingParameterTheory`). Given a framed Hodge moduli space $R$ with parameter
$\pi : R \to \mathbb{A}^1$ (`HodgeRepresentation`) and a complex point $y$ of $R$, there are an
étale map $U \to R$ from a complex scheme with a complex point over $y$, and an étale map
$U \to R_{\pi(y)} \times \mathbb{A}^1$ over $\mathbb{A}^1$, where $R_{\pi(y)}$ is the fibre of $R$
over $\pi(y)$ (`EtaleLocalProduct`). -/
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

/-- Simpson, Theorem 9.1, for the coarse Hodge moduli space: it is étale locally a product with
$\mathbb{A}^1$. Let $X$ be an integral, Noetherian, proper and projective complex variety, smooth of
dimension $d$, with a complex point $x$ and an ample line bundle $H$, and let $n > 0$. Families over
a complex scheme $S$ are framed rank-$n$ relative λ-connections on $X \times S$ over $S$;
admissibility (`IsAdmissible`) is taken for the given pullback system with its coherence, unit-fibre
comparison and fibre tests, and the given dualizing complexes, proper pullbacks and characteristic
class theory. Assume admissibility stable under reindexing and under change of frame and scaling
(`ReindexingProofs`, `ActionAdmissibility`), and fix the given frame structures on $\mathrm{GL}_n$
and $\mathrm{GL}_1$ and scaling action of $\mathrm{GL}_1$ on $\mathbb{A}^1$ (`FrameTheory`,
`ScalingParameterTheory`). Given the framed and coarse Hodge moduli spaces $R \to M$
(`HodgeRepresentation`, `HodgeQuotient`), with parameter $\pi : M \to \mathbb{A}^1$, and a complex
point $y$ of $M$, there are an étale map $U \to M$ from a complex scheme with a complex point over
$y$, and an étale map $U \to M_{\pi(y)} \times \mathbb{A}^1$ over $\mathbb{A}^1$, where $M_{\pi(y)}$
is the fibre of $M$ over $\pi(y)$ (`EtaleLocalProduct`). -/
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
