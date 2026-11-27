/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FlagWeightLineBundles
public import MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses

/-!
# Actual all-rank Schubert classes and the Chevalley expression

Schubert classes are the images of the actual local-length fundamental
cycles of the determinantal Schubert schemes through the existing native
Chow quotient and normalized Betti cycle realization. The weight Chern
class uses the actual projective-bundle inverse formula on the actual weight
line, rather than an independent class-valued assignment. The Chevalley
right side is the finite sum over literal permutation covers, with source
coefficients lambda_i-lambda_j and the actual cohomological degree casts.

Source: Brion, math/0410240v1, Proposition 1.4.3 and section 1.3.
Ordinary cycle/Chern constructions retain their pinned Stacks/Mathlib
attribution in the imported modules. Their providers are dependencies,
separate from the requested Schubert identities.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralSchubertClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralFlagSchemes SchubertRankSchemes FlagWeightLineBundles PerverseSheaves
open BettiCycleRealization ComplexAnalytification AlgebraicBundleGeometry
open CompactSupportBetti ProperBettiFunctoriality

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
  (C : CycleMap D P)

variable {n : ℕ} (F : FlagSchemeModel n (fullShape n))

instance schubertInclusion_closed {w : Equiv.Perm (Fin n)} {side : Bool}
    (S : SchubertIdealModel F w side) : IsClosedImmersion S.inclusion.left :=
  inferInstanceAs (IsClosedImmersion S.ideal.subschemeι)

def schubertClass (w : Equiv.Perm (Fin n)) (S : SchubertIdealModel F w false)
    [IsNoetherian S.scheme.left] :
    BettiRealization.Cohomology (space F.scheme)
      (2 * (flagDimension (fullShape n) : ℤ) - 2 * (length w : ℤ)) :=
  C.cohomologyClass F.scheme (flagDimension (fullShape n)) (length w) F.projective
    ((GeometricChow.rationalEquivalences F.scheme (length w)).mkQ
      (pushedFundamentalCycle S.inclusion (length w)))

abbrev Cover {n : ℕ} (w : Equiv.Perm (Fin n)) :=
  {ij : Fin n × Fin n // downwardCover w ij.1 ij.2}

variable (S : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w false)
  [∀ w, IsNoetherian (S w).scheme.left]

def chevalleySum (weight : Fin n → ℤ) (w : Equiv.Perm (Fin n)) :
    BettiRealization.Cohomology (space F.scheme)
      (2 * (flagDimension (fullShape n) : ℤ) - 2 * (length w : ℤ) + 2) :=
  by
    classical
    exact ∑ c : Cover w, ((weight c.val.1 - weight c.val.2 : ℤ) : ℚ) •
      cohomologyCast (by have h := c.property.2.2; omega)
        (schubertClass D P C F (w * Equiv.swap c.val.1 c.val.2) (S _))

def weightChern
    (T : BettiCharacteristicClasses.ProjectiveBundleTheory D P) (weight : Fin n → ℤ)
    (L : WeightLine F weight)
    (B : ProjectiveBundle F.scheme (flagDimension (fullShape n)) 0 L.object)
    (V : LineTotalSpace B.total (flagDimension (fullShape n)) B.tautological) :
    BettiRealization.Cohomology (space F.scheme) 2 :=
  BettiCharacteristicClasses.chern D P (flagDimension (fullShape n)) 0 L.object B V T 1

end MathlibExt.AlgebraicGeometry.GeneralSchubertClasses
