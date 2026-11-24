/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Theorems/Thm_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_
iterate_of_apply_eq_mul_add.lean`
and
`P2M/Sol/S_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_
iterate_of_apply_eq_mul_add.lean`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib (https://github.com/leanprover-community/mathlib4):
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Finset.Interval
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Twisted telescoping for an iterated ring endomorphism

If `s x = lam * x + u` and `s` has period `ℓ` (that is, `s^[ℓ] = id`
pointwise; `ℓ` need not be the exact order), the iterates of `x`
telescope into a product-and-sum formula over the orbit of `lam` and `u`.
-/

@[expose] public section

namespace RingHom

private theorem iterate_mul {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ)
    (a b : R) : (⇑s)^[n] (a * b) = (⇑s)^[n] a * (⇑s)^[n] b := by
  rw [← RingHom.coe_pow, map_mul]

private theorem iterate_add {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ)
    (a b : R) : (⇑s)^[n] (a + b) = (⇑s)^[n] a + (⇑s)^[n] b := by
  rw [← RingHom.coe_pow, map_add]

private theorem iterate_eq {R : Type*} [CommRing R] (s : R →+* R) (x lam u : R)
    (h : s x = lam * x + u) (n : ℕ) :
    (⇑s)^[n] x = (∏ i ∈ Finset.range n, (⇑s)^[i] lam) * x +
      ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) n, (⇑s)^[i] lam) * (⇑s)^[j] u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∑ j ∈ Finset.range n, (⇑s)^[n] lam *
        ((∏ i ∈ Finset.Ico (j + 1) n, (⇑s)^[i] lam) * (⇑s)^[j] u) =
        ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) (n + 1), (⇑s)^[i] lam) * (⇑s)^[j] u := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j + 1 ≤ n := Finset.mem_range.mp hj
      rw [Finset.prod_Ico_succ_top hj']
      ring
    rw [Function.iterate_succ_apply, h, iterate_add, iterate_mul, ih, Finset.prod_range_succ,
      Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, one_mul, mul_add,
      Finset.mul_sum, key]
    ring

/-- Twisted telescoping: if `s^[ℓ] = id` and `s x = lam * x + u`, then
`(1 - ∏ i < ℓ, s^[i] lam) * x` equals the sum over the orbit of `u` weighted
by later iterates of `lam`. -/
public theorem one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add
    (R : Type*) [CommRing R] (s : R →+* R) (ℓ : ℕ) (hs : ∀ r : R, (⇑s)^[ℓ] r = r)
    (x lam u : R) (h : s x = lam * x + u) :
    (1 - ∏ i ∈ Finset.range ℓ, (⇑s)^[i] lam) * x =
      ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, (⇑s)^[i] lam) * (⇑s)^[j] u := by
  have key := iterate_eq s x lam u h ℓ
  rw [hs] at key
  linear_combination key

end RingHom
