/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.MonicIrreducibleCount

/-!
# Tests for counting monic irreducible polynomials over a finite field
-/

@[expose] public section

open Polynomial FiniteField

/-! ### Values over `𝔽₂`, read off from Gauss's formula -/

example : monicIrreducibleCount (ZMod 2) 1 = 2 := by
  simpa using sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 1) one_ne_zero

-- `x² + x + 1` is the only monic irreducible quadratic over `𝔽₂`.
example : monicIrreducibleCount (ZMod 2) 2 = 1 := by
  have h1 := sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 1) one_ne_zero
  have h2 := sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 2) two_ne_zero
  rw [Nat.Prime.sum_divisors Nat.prime_two] at h2
  simp at h1
  omega

example : monicIrreducibleCount (ZMod 2) 4 = 3 := by
  have h1 := sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 1) one_ne_zero
  have h2 := sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 2) two_ne_zero
  have h4 := sum_divisors_mul_monicIrreducibleCount_zmod 2 (n := 4) (by norm_num)
  rw [Nat.Prime.sum_divisors Nat.prime_two] at h2
  rw [show (4 : ℕ).divisors = {1, 2, 4} by decide] at h4
  simp at h1 h2 h4
  omega

/-! ### Boundary values -/

-- Degree `0`: the only monic constant is `1`, which is a unit.
example (K : Type*) [Field K] : monicIrreducibleCount K 0 = 0 := by
  rw [monicIrreducibleCount, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨f, hm, hi, hd⟩
  rw [eq_one_of_monic_natDegree_zero hm hd] at hi
  exact hi.not_isUnit isUnit_one

-- Junk value: over an infinite field the count is the `Nat.card` of an infinite type, i.e. `0`.
example : monicIrreducibleCount ℚ 1 = 0 := by
  have : Infinite {f : ℚ[X] // f.Monic ∧ Irreducible f ∧ f.natDegree = 1} :=
    Infinite.of_injective
      (fun a : ℚ => ⟨X - C a, monic_X_sub_C a, irreducible_of_degree_eq_one (degree_X_sub_C a),
        natDegree_X_sub_C a⟩)
      fun a b h => by simpa using congrArg (fun f => -(Subtype.val f).coeff 0) h
  exact Nat.card_eq_zero_of_infinite

example : {f : (ZMod 3)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = 5}.Finite :=
  finite_setOf_monic_irreducible_natDegree_eq _ 5
