/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemialgebraicMaps
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Real algebraic strata and actual embedded vector bundles

The real locus is an actual Zariski locally closed polynomial set. Regular functions are locally
rational on actual real Zariski basic opens; they are not arbitrary Nash or
semialgebraic functions. Nonsingularity asks the local ring of the stratum's
Zariski closure to be regular at every point of the stratum. Bundles are images of
continuous idempotent matrices, and their isomorphisms are actual continuous
fibre-linear inverse matrices. Algebraicity is the regularity of the
Grassmannian/projector entries.
Stratified-algebraic isomorphisms additionally require the forward and
inverse matrices to be entrywise regular on an actual common refinement.

Source: Kucharz--Kurdyka, 1308.4376v1, Definitions 1.1--1.2 and Theorem 1.5.
The continuous-projection image bundle and finite-dimensional bundle
embedding primitives are completed TauCeti source support; semialgebraic
projection is not used here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata

open MvPolynomial Set
open scoped Matrix

abbrev Ambient (n : ℕ) := Fin n → ℝ

/-- An embedded real algebraic variety is an actual locally closed locus. -/
structure RealVariety (n : ℕ) where
  closedIdeal : Ideal (MvPolynomial (Fin n) ℝ)
  excludedIdeal : Ideal (MvPolynomial (Fin n) ℝ)

/-- The real points of the variety: the points of $\mathbb{R}^n$ at which every polynomial of the
closed ideal vanishes, minus those at which every polynomial of the excluded ideal vanishes. -/
def RealVariety.locus {n : ℕ} (X : RealVariety n) : Set (Ambient n) :=
  zeroLocus ℝ X.closedIdeal \ zeroLocus ℝ X.excludedIdeal

/-- The coordinate ring of the Zariski closure of a set $S \subseteq \mathbb{R}^n$: real
polynomials in $n$ variables modulo the ideal of polynomials vanishing on $S$. -/
abbrev CoordinateRing {n : ℕ} (S : Set (Ambient n)) :=
  MvPolynomial (Fin n) ℝ ⧸ vanishingIdeal ℝ S

/-- Evaluation of the coordinate ring at a point of `S`. -/
def pointEvaluation {n : ℕ} {S : Set (Ambient n)} (x : S) : CoordinateRing S →+* ℝ :=
  Ideal.Quotient.lift (vanishingIdeal ℝ S) (eval x.val)
    (fun p hp ↦ by simpa [coe_aeval_eq_eval] using hp x.val x.property)

instance pointPrime {n : ℕ} {S : Set (Ambient n)} (x : S) :
    (RingHom.ker (pointEvaluation x)).IsPrime :=
  RingHom.ker_isPrime (pointEvaluation x)

abbrev LocalRing {n : ℕ} {S : Set (Ambient n)} (x : S) :=
  Localization.AtPrime (RingHom.ker (pointEvaluation x))

def Nonsingular {n : ℕ} (S : Set (Ambient n)) : Prop :=
  ∀ x : S, IsRegularLocalRing (LocalRing x)

def IsZariskiLocallyClosed {n : ℕ} (X : RealVariety n) (S : Set (Ambient n)) : Prop :=
  ∃ I J : Ideal (MvPolynomial (Fin n) ℝ),
    S = X.locus ∩ (zeroLocus ℝ I \ zeroLocus ℝ J)

/-- Local rationality on D(q), with no replacement by a semialgebraic predicate. -/
def RegularOn {n : ℕ} (S : Set (Ambient n)) (f : Ambient n → ℝ) : Prop :=
  ∀ x ∈ S, ∃ p q : MvPolynomial (Fin n) ℝ, eval x q ≠ 0 ∧
    ∀ y ∈ S, eval y q ≠ 0 → f y * eval y q = eval y p

structure Stratification {n : ℕ} (X : RealVariety n) where
  count : ℕ
  stratum : Fin count → Set (Ambient n)
  locallyClosed : ∀ i, IsZariskiLocallyClosed X (stratum i)
  nonempty : ∀ i, (stratum i).Nonempty
  disjoint : Pairwise fun i j ↦ Disjoint (stratum i) (stratum j)
  covers : ⋃ i, stratum i = X.locus

def Stratification.nonsingular {n : ℕ} {X : RealVariety n} (S : Stratification X) : Prop :=
  ∀ i, Nonsingular (S.stratum i)

def Refines {n : ℕ} {X : RealVariety n} (S T : Stratification X) : Prop :=
  ∀ i, ∃ j, S.stratum i ⊆ T.stratum j

/-- Actual orthogonal-projection image bundles in the trivial real bundle. -/
structure ProjectionBundle {n : ℕ} (X : RealVariety n) (r : ℕ) where
  projection : X.locus → Matrix (Fin r) (Fin r) ℝ
  continuous : Continuous projection
  idempotent : ∀ x, projection x * projection x = projection x
  symmetric : ∀ x, (projection x).transpose = projection x

def ProjectionBundle.fiber {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) (x : X.locus) : Submodule ℝ (Fin r → ℝ) :=
  LinearMap.range (Matrix.toLin' (P.projection x))

/-- Continuous matrices give actual inverse maps on the two image fibres. -/
structure BundleIso {n : ℕ} {X : RealVariety n} {r s : ℕ}
    (P : ProjectionBundle X r) (Q : ProjectionBundle X s) where
  forward : X.locus → Matrix (Fin s) (Fin r) ℝ
  inverse : X.locus → Matrix (Fin r) (Fin s) ℝ
  forward_continuous : Continuous forward
  inverse_continuous : Continuous inverse
  preserves : ∀ x, Q.projection x * forward x = forward x ∧
    forward x * P.projection x = forward x
  inverse_preserves : ∀ x, P.projection x * inverse x = inverse x ∧
    inverse x * Q.projection x = inverse x
  left : ∀ x, inverse x * forward x = P.projection x
  right : ∀ x, forward x * inverse x = Q.projection x

def EntrywiseRegularOn {n : ℕ} {X : RealVariety n} {r s : ℕ}
    (a : X.locus → Matrix (Fin r) (Fin s) ℝ) (S : Set (Ambient n)) : Prop :=
  S ⊆ X.locus ∧ ∀ i j,
    ∀ (f : Ambient n → ℝ), (∀ x : X.locus, f x.val = a x i j) →
      RegularOn S f

def IsAlgebraicOn {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) (S : Set (Ambient n)) : Prop :=
  EntrywiseRegularOn P.projection S

def IsAlgebraicFor {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) (S : Stratification X) : Prop :=
  ∀ i, IsAlgebraicOn P (S.stratum i)

def IsStratifiedAlgebraic {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) : Prop :=
  ∃ S : Stratification X, IsAlgebraicFor P S

/-- Topological admission of some structure is weaker than being an
object of the stratified-algebraic category on the specified projector. -/
def AdmitsStratifiedAlgebraicStructure {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) : Prop :=
  ∃ (s : ℕ) (Q : ProjectionBundle X s), Nonempty (BundleIso P Q) ∧
    ∃ S : Stratification X, IsAlgebraicFor Q S

/-- Both fibre maps are real-regular on the common actual strata. -/
def IsAlgebraicIsoFor {n : ℕ} {X : RealVariety n} {r s : ℕ}
    {P : ProjectionBundle X r} {Q : ProjectionBundle X s}
    (a : BundleIso P Q) (S : Stratification X) : Prop :=
  IsAlgebraicFor P S ∧ IsAlgebraicFor Q S ∧
    ∀ i, EntrywiseRegularOn a.forward (S.stratum i) ∧
      EntrywiseRegularOn a.inverse (S.stratum i)

def IsStratifiedAlgebraicIso {n : ℕ} {X : RealVariety n} {r s : ℕ}
    {P : ProjectionBundle X r} {Q : ProjectionBundle X s} (a : BundleIso P Q) : Prop :=
  ∃ S : Stratification X, IsAlgebraicIsoFor a S

end MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata
