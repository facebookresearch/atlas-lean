/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeLambdaPullbackSystems

/-!
# Actual fibre tests and arbitrary-base admissible lambda families

The fibre is obtained by the native framed family pullback to a complex
point and the actual unit-product/absolute differential comparison. The
connection, both operators and parameter are normalized on these native
pullbacks. Stability tests actual invariant coherent torsion-free
subsheaves. At lambda zero, every positive rational Chern class is the
existing native Betti characteristic class, with its actual projective
geometry. No Hilbert-coefficient proxy replaces these Chern conditions.

The complex-point test is made on finite type complex presentations.
On an arbitrary parameter scheme T, admissibility is local descent from
those presentations, with an actual parameter/bundle/BOTH-operator/frame
`Family.Iso` to the native pulled-back family. Testing only complex points
of arbitrary T would be incorrect, for example for Spec C(t).

Source: Simpson, alg-geom/9604005v1, section 4 and Proposition 4.1;
finite presentation and filtered-limit descent of vector bundles, differential
operators and frames (the standard source comparison is a separate target).
The imported module/cohomology/Chern constructions retain their pinned
Mathlib/Stacks author, revision and Apache license attribution.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdmissibleRelativeLambdaFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory Opposite
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaReindexing RelativeLambdaPullbackSystems
open RelativeDeRhamDifferential RelativeDifferentialForms AlgebraicLambdaConnections
open PolarizedHiggsStability ProjectiveLineSystems RationalChernZeroHiggsBundles

abbrev scalarBase : ComplexScheme := 𝟙_ ComplexScheme
abbrev unitProduct (X : ComplexScheme) : ComplexScheme := prod X scalarBase

variable (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) (P : PullbackSystem X x n)

/-- The comparison is the actual identity on X×unit and inverse of the
unit's structure morphism, with normalized forms and BOTH operators. -/
structure UnitFibreComparison where
  differential : Differential (unitProduct X).hom
  square : RelativeSquare (projection X scalarBase) (unitProduct X).hom
  total_eq : square.total = 𝟙 (unitProduct X).left
  scalar_right : square.base ≫ scalarBase.hom = 𝟙 _
  scalar_left : scalarBase.hom ≫ square.base = 𝟙 _
  tensor : TensorPullbackComparison square.total
  forms : FormBaseChange square tensor (P.differential scalarBase) differential
  lift : ∀ E : Family X x scalarBase (P.differential scalarBase) n,
    PulledConnection square tensor forms E.connection

def UnitFibreComparison.parameter (V : UnitFibreComparison X x n P)
    (E : Family X x scalarBase (P.differential scalarBase) n) : Γ(Spec (CommRingCat.of ℂ), ⊤) :=
  V.square.parameter E.parameter

def UnitFibreComparison.absolute (V : UnitFibreComparison X x n P)
    (E : Family X x scalarBase (P.differential scalarBase) n) :
    LambdaConnection (unitProduct X).hom (V.parameter X x n P E) V.differential :=
  (V.lift E).connection

variable (V : UnitFibreComparison X x n P) (d : ℕ) (H : LineBundle X.left)

structure FibreTests where
  polarization : LineBundle (unitProduct X).left
  polarizationIso : polarization.val ≅
    (Scheme.Modules.pullback (prod.fst : unitProduct X ⟶ X).left).obj H.val
  [noetherian : IsNoetherian (unitProduct X).left]
  ample : IsAmpleLine polarization
  numerics : HilbertNumerics (unitProduct X) polarization d
  coherent : ∀ E : Family X x scalarBase (P.differential scalarBase) n,
    NumericalCompactifiedJacobians.IsFiniteTypeQuasicoherent (V.absolute X x n P E).object
  chern : ∀ E : Family X x scalarBase (P.differential scalarBase) n,
    ChernGeometry (unitProduct X) d (V.absolute X x n P E).rank (V.absolute X x n P E).object

/-- The fixed-rank Hilbert polynomial is computed from actual fibre
cohomology and the actual structure sheaf, rather than supplied as a proxy. -/
def HasRankHilbertPolynomial (F : FibreTests X x n P V d H)
    (hO : NumericalCompactifiedJacobians.IsFiniteTypeQuasicoherent
      (CoherentCurveLinearSeries.structureModule (unitProduct X).left))
    (E : Family X x scalarBase (P.differential scalarBase) n) : Prop :=
  F.numerics.polynomial (V.absolute X x n P E).object (F.coherent E) =
    (n : ℚ) • F.numerics.polynomial
      (CoherentCurveLinearSeries.structureModule (unitProduct X).left) hO

def coherentFibre (F : FibreTests X x n P V d H)
    (E : Family X x scalarBase (P.differential scalarBase) n) :
    LambdaConnectionStability.CoherentConnection (unitProduct X).hom
      (V.parameter X x n P E) V.differential where
  connection := V.absolute X x n P E
  coherent := F.coherent E

variable
  (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
  (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
    (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
  (T : BettiCharacteristicClasses.ProjectiveBundleTheory D Q)
  [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
  (F : FibreTests X x n P V d H)

def FiniteTypeAdmissible {S : ComplexScheme} (E : Family X x S (P.differential S) n) : Prop :=
  LocallyOfFiniteType S.hom ∧ QuasiCompact S.hom ∧
  ∀ t : scalarBase ⟶ S,
    LambdaConnectionStability.IsSemistable F.numerics (coherentFibre X x n P V d H F (P.pull X
      x n t E)) ∧
    (V.parameter X x n P (P.pull X x n t E) = 0 →
      AllRationalChernZero D Q T (F.chern (P.pull X x n t E)))

/-- Local finite type data on EVERY scheme point, including points which
are not complex-valued. Each comparison is a full actual family isomorphism. -/
structure AdmissiblePresentation {S : ComplexScheme} (E : Family X x S (P.differential S) n) where
  opens : S.left → S.left.Opens
  contains : ∀ s, s ∈ opens s
  base : S.left → ComplexScheme
  map : ∀ s, openBase S (opens s) ⟶ base s
  family : ∀ s, Family X x (base s) (P.differential (base s)) n
  admissible : ∀ s, FiniteTypeAdmissible X x n P V d H D Q T F (family s)
  comparison : ∀ s,
    Family.Iso (restrictFamily X x n P E (opens s)) (P.pull X x n (map s) (family s))

def IsAdmissible {S : ComplexScheme} (E : Family X x S (P.differential S) n) : Prop :=
  Nonempty (AdmissiblePresentation X x n P V d H D Q T F E)

end MathlibExt.AlgebraicGeometry.AdmissibleRelativeLambdaFamilies
