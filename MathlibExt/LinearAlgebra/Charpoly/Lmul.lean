/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Minimal polynomial equals left-multiplication characteristic polynomial

Let K be a field, E a finite-dimensional K-algebra whose underlying ring may be
noncommutative, and x∈E. If deg(minpoly_K(x))=dim_K(E), then χ_(L_x)=minpoly_K(x).
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace LinearMap

section Primitive

variable {K E : Type*} [Field K] [Ring E] [Algebra K E]
  [FiniteDimensional K E]

/-- **Full-degree minimal polynomial is the left-multiplication characteristic polynomial.**

Let K be a field, E a finite-dimensional K-algebra with a ring structure and x∈E. If the
natural degree of minpoly K x equals finrank_K E, then (Algebra.lmul K E x).charpoly=minpoly K
x.
-/
theorem charpoly_lmul_eq_minpoly_of_natDegree_eq_finrank
    (x : E) (hDeg : (minpoly K x).natDegree = Module.finrank K E) :
    (Algebra.lmul K E x).charpoly = minpoly K x := by
  have hdvd : minpoly K x ∣ (Algebra.lmul K E x).charpoly :=
    minpoly.dvd K x (Algebra.aeval_self_charpoly_lmul x)
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite K x)) (charpoly_monic _) hdvd
  rw [charpoly_natDegree, hDeg]

end Primitive

end LinearMap
