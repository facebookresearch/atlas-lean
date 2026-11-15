/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The structural morphism follows the completed Atlas
MathlibExt/AlgebraicGeometry/ProjectiveDirectImage.lean adapter of
leanprover/lean-eval, revision 38361be884302c7edce1908c4aef8296eb2cb27e,
namespace LeanEval.AlgebraicGeometry.TopologicalReconstruction,
Apache 2.0. This records the source attribution of that Atlas adapter.
Modification: use arbitrary commutative rings and actual polynomial Proj
without the complex realization or derived-direct-image imports.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial projectivity over an arbitrary ring

The projective ambient space is the actual homogeneous-polynomial Proj
over the supplied ring. A projective model includes an actual closed
immersion over that base. This is the general-ring version of the
completed Atlas gradedProjToSpec/projectivity definition; no field or
analytic realization is needed for integral model geometry.

References: Stacks Project, Tags01ND and01N7; native Mathlib Proj.toSpecZero.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective spectrum of the polynomial grading over any ring. -/
def projectiveSpace (R : CommRingCat.{0}) (n : ℕ) : Over (Spec R) :=
  Over.mk (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ..)))

/-- Projectivity is an actual closed immersion into this polynomial Proj. -/
def IsProjective {R : CommRingCat.{0}} {X : Scheme.{0}} (π : X ⟶ Spec R) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ (projectiveSpace R n).left),
    IsClosedImmersion i ∧ π = i ≫ (projectiveSpace R n).hom

end MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity
