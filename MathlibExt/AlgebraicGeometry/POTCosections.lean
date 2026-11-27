/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.POTVirtualPullback

/-!
# Literal affine POT cosections and their degeneracy schemes

A cycle vector in E⁻¹ defines evaluation on (E⁻¹)∨, which factors through
the actual obstruction quotient coker(d∨). Its degeneracy ideal is generated
by its coordinate values. The degeneracy scheme and closed push are actual
Spec/quotient and geometric-cycle constructions. The candidate localized
class is an element of this actual Chow quotient whose push equals the
already computed POT cone class; no separate virtual-class operator is input.

Reference: Kiem--Li, *Localizing virtual cycles by cosections*,
https://arxiv.org/abs/1007.3085, §§4--5. Generic Koszul cosection resolutions
and localized Chern operations are complete in AxiomMath/Stacks and are not
asserted as new constructions here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.POTCosections

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AffineConeAtlas
open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open MathlibExt.AlgebraicGeometry.GeometricChowOperators
open MathlibExt.AlgebraicGeometry.POTVirtualPullback

variable {B : Type} [CommRing B] [Algebra ℂ B]
    {P : _root_.Algebra.Extension.{0} ℂ B} (F : ConePresentation P)

abbrev presentationModel : FreeTwoTerm B :=
  ⟨F.negativeRank, F.zeroRank, F.differential⟩

/-- The finite-free bidual writes an actual obstruction cosection as a cycle vector. -/
structure Cosection where
  vector : Fin F.negativeRank → B
  cycle : F.differential vector = 0

def vectorEvaluation (s : Cosection F) :
    ((Fin F.negativeRank → B) →ₗ[B] B) →ₗ[B] B where
  toFun a := a s.vector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation descends to the literal obstruction module. -/
def obstructionCosection (s : Cosection F) :
    ObstructionModule (presentationModel F) B →ₗ[B] B :=
  (LinearMap.range (dualDifferential (presentationModel F) B)).liftQ
    (vectorEvaluation F s) (by
      intro a ha
      obtain ⟨b, rfl⟩ := ha
      change b (F.differential s.vector) = 0
      rw [s.cycle, map_zero])

@[simp] theorem obstructionCosection_mk (s : Cosection F)
    (a : (Fin F.negativeRank → B) →ₗ[B] B) :
    obstructionCosection F s
      ((LinearMap.range (dualDifferential (presentationModel F) B)).mkQ a) = a s.vector := rfl

def degeneracyIdeal (s : Cosection F) : Ideal B := Ideal.span (Set.range s.vector)

/-- The linear equation of the cosection on the actual obstruction bundle. -/
def bundleEquation (s : Cosection F) : bundleRing F :=
  SymmetricAlgebra.ι B (Fin F.negativeRank → B) s.vector

variable [IsNoetherianRing B]

def degeneracy (s : Cosection F) : MathlibExt.AlgebraicGeometry.GeometricChow.ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (degeneracyIdeal F s))) ≫
    (baseScheme (B := B)).hom)

def degeneracyMap (s : Cosection F) : degeneracy F s ⟶ baseScheme (B := B) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (degeneracyIdeal F s)))) rfl

instance degeneracyClosed (s : Cosection F) : IsClosedImmersion (degeneracyMap F s).left :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (degeneracyIdeal F s))) Ideal.Quotient.mk_surjective

instance degeneracyNoetherian (s : Cosection F) : IsNoetherian (degeneracy F s).left := by
  change IsNoetherian (Spec (.of (B ⧸ degeneracyIdeal F s)))
  infer_instance

/-- This is a refinement in the actual supported Chow group. Its existence
is the localization target, not an assumed virtual-class theory. -/
def LocalizedVirtualClass (s : Cosection F)
    (D : ChowPullbackEquivalence (baseScheme (B := B)) (bundleScheme F)
      (bundleMap F) F.negativeRank)
    (J : ClosedCycleDescent (bundleScheme F) (coneMap F))
    (K : ClosedCycleDescent (baseScheme (B := B)) (degeneracyMap F s)) :=
  {c : gradedChow (degeneracy F s) ((F.zeroRank : ℤ) - F.negativeRank) //
    gradedClosedPush (baseScheme (B := B)) (degeneracyMap F s) K
      ((F.zeroRank : ℤ) - F.negativeRank) c = classFromCone F D J}

end MathlibExt.AlgebraicGeometry.POTCosections
