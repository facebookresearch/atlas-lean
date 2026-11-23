/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ProjectiveSpace

universe u

variable {k : Type u} [Field k]

-- `ℙⁿ_k` lies over `Spec k` through the structure morphism of its projective spectrum.
example (n : ℕ) :
    (projectiveSpace k n).hom =
      letI := @MvPolynomial.gradedAlgebra
      projToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := rfl

-- Projective space itself is projective, through the identity closed immersion.
example (n : ℕ) : IsProjective (projectiveSpace k n) :=
  ⟨n, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance⟩
