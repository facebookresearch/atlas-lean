/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

/-!
# Polynomial projectivity over an arbitrary ring

The projective ambient space is the actual homogeneous-polynomial Proj
over the supplied ring, with the structure morphism
`ProjectiveSpace.projToSpec`, and projectivity is
`ProjectiveSpace.IsProjectiveHom`: an actual closed immersion into such a
Proj over the base. No field or analytic realization is needed for integral
model geometry.

References: Stacks Project, Tags01ND and01N7; native Mathlib Proj.toSpecZero.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective spectrum of the polynomial grading over any ring, over `Spec R`. -/
def projectiveSpace (R : CommRingCat.{0}) (n : ℕ) : Over (Spec R) :=
  Over.mk (ProjectiveSpace.projToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))

/-- Projectivity is an actual closed immersion into a polynomial Proj:
`ProjectiveSpace.IsProjectiveHom`. -/
abbrev IsProjective {R : CommRingCat.{0}} {X : Scheme.{0}} (π : X ⟶ Spec R) : Prop :=
  ProjectiveSpace.IsProjectiveHom (R := R) π

end MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity
