/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjSpace

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

example (R : Type u) [CommRing R] (n : ℕ) : IsProper (ProjSpace.π R n) := inferInstance

example (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    (ProjSpace.grad0Equiv R n).symm (ProjSpace.grad0Equiv R n r) = r := by
  simp

example (R : Type u) [CommRing R] (n : ℕ) (r : R) :
    ((ProjSpace.grad0Equiv R n r : homogeneousSubmodule (Fin (n + 1)) R 0) :
      MvPolynomial (Fin (n + 1)) R) = C r :=
  ProjSpace.grad0Equiv_apply_coe R n r
