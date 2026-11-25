/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity` -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity

namespace MathlibExtTest.AlgebraicGeometry.RelativePolynomialProjectivity

/-- Projectivity over a ring is the shared projectivity predicate. -/
example {R : CommRingCat.{0}} {X : Scheme.{0}} (π : X ⟶ Spec R) :
    IsProjective π ↔ ProjectiveSpace.IsProjectiveHom (R := R) π :=
  Iff.rfl

/-- Projective space over a ring lies over `Spec R` by the shared structure morphism. -/
example (R : CommRingCat.{0}) (n : ℕ) :
    (projectiveSpace R n).hom =
      letI := @MvPolynomial.gradedAlgebra
      ProjectiveSpace.projToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  rfl

/-- Projective space over a ring is projective, through the identity. -/
example (R : CommRingCat.{0}) (n : ℕ) : IsProjective (projectiveSpace R n).hom :=
  ⟨n + 1, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance, (Category.id_comp _).symm⟩

end MathlibExtTest.AlgebraicGeometry.RelativePolynomialProjectivity

end
