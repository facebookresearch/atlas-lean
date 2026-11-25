/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.AdjoinRootPowSub

@[expose] public section

open Polynomial

universe u v

private theorem exactSource
    {R : Type u} [CommRing R] (n : ℕ) (u : R) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) :=
  AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n u hn hu

-- Higher-universe consumer.
example
    {R : Type (u + 1)} [CommRing R] (n : ℕ) (u : R) (hn : IsUnit (n : R))
    (hu : IsUnit u) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) :=
  AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n u hn hu

-- Boundary: when `n = 0` and the base is nontrivial, `(n : R)` is not a
-- unit, so the hypothesis fails; adjoining a root is not covered.
example {R : Type u} [CommRing R] [Nontrivial R] : ¬ IsUnit ((0 : ℕ) : R) := by
  simp
