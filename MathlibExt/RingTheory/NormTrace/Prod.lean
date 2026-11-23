/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_norm_prod.lean`,
`P2M/Sol/S_Algebra_norm_prod.lean`,
`Theorems/Thm_Algebra_norm_of_subsingleton.lean` and
`P2M/Sol/S_Algebra_norm_of_subsingleton.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Norm.Basic

/-!
# Norms over product algebras and subsingleton algebras

The norm of a product algebra splits as the product of the norms, and the
norm on a subsingleton algebra is constantly `1`.
-/

@[expose] public section

/-- The norm of a product algebra is the product of the norms of the
components: left multiplication by `(x₁, x₂)` is the product map of the
left multiplications, and the determinant of a product map is the product
of the determinants. -/
theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]

/-- The norm on a subsingleton algebra is `1`: left multiplication by any
element is the identity map on a subsingleton module, hence has determinant
`1`. -/
theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _
