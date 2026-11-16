/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapSectionLengths
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The actual homogeneous invariant algebra of a character polarization

The algebra carrier is the direct sum of the actual invariant-section
coefficient subgroups, retaining the homogeneous degree. Its
multiplication is fixed on every pair of homogeneous generators by
ordinary multiplication of their regular functions. This construction
also covers a trivial or torsion character, when the same regular
function occurs in several degrees.

The GIT target is the native Proj of this particular graded algebra.
The affine quotient is Spec of the actual invariant regular-function
ring, and its proper projection is recorded as genuine scheme geometry.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2, §2.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open LinearizedLineBundles LineBundleTaskContracts CoherentCurveLinearSeries
open QuasimapBasepointDefects QuasimapSectionLengths

universe u
variable {S : Scheme.{u}} (G W : Over S) [GrpObj G] [ModObj G W]
variable (L : CharacterPolarization G W)

/-- The actual invariant coefficient subgroup in degree m. -/
def invariantPiece (m : ℕ) : AddSubgroup Γ(W.left, ⊤) :=
  AddSubgroup.closure {f | ∃ s : Section (power L.line.module m),
    IsInvariantPowerSection G W L.line.linearization L.actionPowers L.projectionPowers m s ∧
      invariantCoefficient L m s = f}

abbrev InvariantAlgebra := DirectSum ℕ (fun m => ↥(invariantPiece G W L m))

/-- The component-supported native homogeneous subgroup of the actual direct sum. -/
def invariantGrading (m : ℕ) : AddSubgroup (InvariantAlgebra G W L) where
  carrier := {x | ∀ n, n ≠ m → x n = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb n hn := by simp [ha n hn, hb n hn]
  neg_mem' {x} ha n hn := by
    change -(x n) = 0
    rw [ha n hn, neg_zero]

/-- Native ring and grading assembly, with its full homogeneous multiplication fixed. -/
class InvariantAlgebraModel where
  [products : SetLike.GradedMonoid (invariantPiece G W L)]
  [grading : GradedRing (invariantGrading G W L)]
  zeroComparison : invariantGrading G W L 0 ≃+* invariantRing G W
  zero_normalized : ∀ a : invariantGrading G W L 0,
    (zeroComparison a).val = (a.val 0).val

attribute [instance] InvariantAlgebraModel.products
attribute [instance_reducible] InvariantAlgebraModel.grading
attribute [instance] InvariantAlgebraModel.grading

/-- The actual projective GIT quotient of the chosen invariant algebra. -/
abbrev gitScheme [InvariantAlgebraModel G W L] := Proj (invariantGrading G W L)

/-- The actual affine invariant-function quotient. -/
abbrev affineQuotient := Spec (.of (invariantRing G W))

/-- The affine-quotient arrow is the native degree-zero Proj structure map. -/
def gitAffineProjection [A : InvariantAlgebraModel G W L] :
    gitScheme G W L ⟶ affineQuotient G W :=
  Proj.toSpecZero (invariantGrading G W L) ≫
    Spec.map (CommRingCat.ofHom A.zeroComparison.symm.toRingHom)

/-- The invariant-coefficient scalar action is the actual degree-zero inclusion. -/
def invariantScalarMap [A : InvariantAlgebraModel G W L] :
    invariantRing G W →+* InvariantAlgebra G W L :=
  (SetLike.GradeZero.subring (invariantGrading G W L)).subtype.comp
    A.zeroComparison.symm.toRingHom

instance invariantAlgebraScalars [InvariantAlgebraModel G W L] :
    Algebra (invariantRing G W) (InvariantAlgebra G W L) :=
  (invariantScalarMap G W L).toAlgebra

/-- Evaluate every homogeneous invariant at the actual stable open. -/
def gitEvaluation [InvariantAlgebraModel G W L] (U : W.left.Opens) :
    InvariantAlgebra G W L →+* Γ(U, ⊤) :=
  U.ι.appTop.hom.comp (DirectSum.coeRingHom (invariantPiece G W L))

/-- The canonical stable-locus map uses the native Proj chart gluing construction. -/
def gitOrbitMap [InvariantAlgebraModel G W L] (U : W.left.Opens)
    (h : (HomogeneousIdeal.irrelevant (invariantGrading G W L)).toIdeal.map
      (gitEvaluation G W L U) = ⊤) : U.toScheme ⟶ gitScheme G W L :=
  Proj.fromOfGlobalSections (invariantGrading G W L) (gitEvaluation G W L U) h

end MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras
