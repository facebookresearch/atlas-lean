/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X.lean`
and
`P2M/Sol/S_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X.lean`
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

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs

@[expose] public section

universe u v

namespace RingEquiv

/-- Two identifications of a ring `R` with `k[X]` cannot interchange the
roles of `X` and `X ^ p` for `p ≥ 2`: composing them would send `X ^ p`
both to `X` and to `X ^ (p * p)`, contradicting degrees. -/
public theorem false_of_apply_eq_X_pow_of_apply_eq_X
    (p : ℕ) (hp : 2 ≤ p) (k : Type v) [CommRing k] [Nontrivial k]
    (R : Type u) [CommRing R] (e₀ e₁ : R ≃+* Polynomial k) (a b : R)
    (h₀a : e₀ a = Polynomial.X) (h₀b : e₀ b = Polynomial.X ^ p)
    (h₁b : e₁ b = Polynomial.X) (h₁a : e₁ a = Polynomial.X ^ p) : False := by
  have ha : e₀.symm Polynomial.X = a := by
    rw [← h₀a, e₀.symm_apply_apply]
  have hb : e₀.symm (Polynomial.X ^ p) = b := by
    rw [← h₀b, e₀.symm_apply_apply]
  have h1 : (e₀.symm.trans e₁) (Polynomial.X ^ p) = Polynomial.X := by
    rw [RingEquiv.trans_apply, hb, h₁b]
  have h2 : (e₀.symm.trans e₁) (Polynomial.X ^ p) = Polynomial.X ^ (p * p) := by
    rw [map_pow, RingEquiv.trans_apply, ha, h₁a, ← pow_mul]
  have h3 := congrArg Polynomial.natDegree (h1.symm.trans h2)
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at h3
  have h4 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
  omega

end RingEquiv
