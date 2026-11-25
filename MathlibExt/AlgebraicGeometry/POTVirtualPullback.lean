/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.AffineConeAtlas
public import MathlibExt.AlgebraicGeometry.GeometricChowOperators
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
/-!
# A computed virtual zero-section pullback on the actual POT cone image

The obstruction bundle is Spec Sym(E⁻¹), and the cone image is Spec of its
quotient by the kernel of the actual POT atlas algebra map. Its closed
inclusion and Noetherianity are proved. The zero-section pullback is the
computed residue-weighted cone push followed by the inverse of the actual
cycle-fibre pullback. It acts on every integer Chow degree. Applying it to
the length-weighted cone cycle in degree rank(E⁰) gives the candidate class
in degree rank(E⁰)−rank(E⁻¹).

The supplied proof inputs concern descent and bijectivity of already
specified cycle maps, not arbitrary Chow or virtual-class operators.
Vector-bundle homotopy invariance and chosen-immersion virtual classes are
source-proved in AxiomMath/Stacks (02TY, 0FBK), revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/AffineBundle/VectorBundleFlatPullback.lean
and Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean.
Those generic statements are not new Wanted claims; the remaining comparison
is the intrinsic POT atlas/stabilization geometry.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.POTVirtualPullback
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow
open MathlibExt.AlgebraicGeometry.GeometricChowOperators
open MathlibExt.AlgebraicGeometry.AffineConeAtlas

variable {B : Type} [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
variable {P : _root_.Algebra.Extension.{0} ℂ B} (F : ConePresentation P)

abbrev bundleRing := SymmetricAlgebra B (Fin F.negativeRank → B)

def baseScheme : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))

def bundleScheme : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap B (bundleRing F))) ≫ (baseScheme (B := B)).hom)

def bundleMap : bundleScheme F ⟶ baseScheme (B := B) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap B (bundleRing F)))) rfl

instance symNoetherian : IsNoetherianRing (bundleRing F) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial (Fin F.negativeRank) B)
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin F.negativeRank))).symm.toRingEquiv

instance baseNoetherian : IsNoetherian (baseScheme (B := B)).left := by
  change IsNoetherian (Spec (.of B))
  infer_instance
instance bundleNoetherian : IsNoetherian (bundleScheme F).left := by
  change IsNoetherian (Spec (.of (bundleRing F)))
  infer_instance

abbrev coneIdeal := RingHom.ker (atlasHom F).toRingHom
abbrev coneRing := bundleRing F ⧸ coneIdeal F

def imageCone : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coneIdeal F))) ≫ (bundleScheme F).hom)

def coneMap : imageCone F ⟶ bundleScheme F :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coneIdeal F)))) rfl

instance imageNoetherian : IsNoetherian (imageCone F).left := by
  change IsNoetherian (Spec (.of (coneRing F)))
  infer_instance
instance coneMapClosed : IsClosedImmersion (coneMap F).left :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (coneIdeal F)))
    Ideal.Quotient.mk_surjective

variable (D : ChowPullbackEquivalence (baseScheme (B := B)) (bundleScheme F)
    (bundleMap F) F.negativeRank)
  (J : ClosedCycleDescent (bundleScheme F) (coneMap F))

def zeroSectionPullback (d : ℤ) :
    gradedChow (imageCone F) d →ₗ[ℚ] gradedChow (baseScheme (B := B)) (d - F.negativeRank) :=
  (pullbackEquiv _ _ _ _ D (d - F.negativeRank)).symm.toLinearMap ∘ₗ
    gradedChowCast (bundleScheme F) (by omega) ∘ₗ
      gradedClosedPush (bundleScheme F) (coneMap F) J d

def classFromCone : gradedChow (baseScheme (B := B)) ((F.zeroRank : ℤ) - F.negativeRank) :=
  zeroSectionPullback F D J F.zeroRank
    ((positiveChowIso (imageCone F) F.zeroRank (by omega)).toLinearEquiv.symm
      ((rationalEquivalences (imageCone F) F.zeroRank).mkQ
        (fundamentalCycleOfDimension (imageCone F).left F.zeroRank)))


/-- The virtual class of a cone presentation `F` that is an obstruction theory
(`IsObstructionTheory`), for a Noetherian $\mathbb{C}$-algebra $B$ and a presentation `P` of $B$ as
a quotient of a $\mathbb{C}$-algebra `P.Ring` (`Algebra.Extension ℂ B`) that is isomorphic to a
polynomial ring over $\mathbb{C}$ in finitely many variables: the class `classFromCone F D J` in the
rational Chow group of $\operatorname{Spec} B$ in degree `F.zeroRank - F.negativeRank`, the
zero-section pullback, through the given `D` and `J`, of the fundamental class of the cone image in
degree `F.zeroRank`. -/
def virtualClass (_valid : IsObstructionTheory F)
    (_polynomial : ∃ n : ℕ, Nonempty (P.Ring ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)) :
    gradedChow (baseScheme (B := B)) ((F.zeroRank : ℤ) - F.negativeRank) :=
  classFromCone F D J

end MathlibExt.AlgebraicGeometry.POTVirtualPullback
