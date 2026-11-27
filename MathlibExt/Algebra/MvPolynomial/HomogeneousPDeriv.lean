/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`
and
`P2M/Sol/S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MvPolynomial

/-- Iterating a partial derivative lowers the homogeneous degree. -/
public theorem IsHomogeneous.iterate_pderiv {σ R : Type*}
    [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ} (k : σ)
    (hφ : φ.IsHomogeneous n) (j : ℕ) :
    ((pderiv k)^[j] φ).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

/-- Differentiating a degree-`n` homogeneous polynomial more than `n`
times in one variable gives zero. -/
public theorem IsHomogeneous.iterate_pderiv_eq_zero_of_lt {σ R : Type*}
    [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (pderiv k)^[i] φ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show n + m + 1 = m + 1 + n by ring, Function.iterate_add_apply,
    Function.iterate_succ_apply]
  have h0 : ((pderiv k)^[n] φ).IsHomogeneous 0 := by
    simpa using hφ.iterate_pderiv k n
  have hC : (pderiv k)^[n] φ = C (((pderiv k)^[n] φ).coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h0.totalDegree_le)
  rw [hC, pderiv_C]
  exact Function.iterate_fixed (map_zero _) m

end MvPolynomial
