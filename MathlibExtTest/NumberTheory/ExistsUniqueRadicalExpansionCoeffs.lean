/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ExistsUniqueRadicalExpansionCoeffs
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Tests for the integer coordinates of powers of `u + v^{1/N}`
-/

namespace MetaMathlibExt.ExistsUniqueRadicalExpansionCoeffsTest

open Polynomial

/-- `X ^ 6 - 2` is irreducible over `ℚ`: it is monic and Eisenstein at `2` over `ℤ`. -/
private lemma irreducible_X_pow_six_sub_two : Irreducible (X ^ 6 - C (2 : ℚ)) := by
  have hmonic : (X ^ 6 - C (2 : ℤ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  have heis : (X ^ 6 - C (2 : ℤ)).IsEisensteinAt (Ideal.span {2}) := by
    refine hmonic.isEisensteinAt_of_mem_of_notMem ?_ (fun {n} hn ↦ ?_) ?_
    · rw [Ne, Ideal.span_singleton_eq_top]
      decide
    · rw [natDegree_X_pow_sub_C] at hn
      rw [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hn.ne]
      split_ifs <;> norm_num
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp
  have hirr : Irreducible (X ^ 6 - C (2 : ℤ)) :=
    heis.irreducible ((Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two)
      hmonic.isPrimitive (by rw [natDegree_X_pow_sub_C]; norm_num)
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).1 hirr
  rwa [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eq_intCast, Int.cast_ofNat] at h

-- The hypotheses hold together: `N = 6`, `u = 1` and `v = 2`.
example (n : ℕ) :
    ∃! a : Fin 6 → ℤ, (((1 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) ^ (1 / ((6 : ℕ) : ℝ))) ^ n =
      ∑ i : Fin 6, (a i : ℝ) * (((2 : ℕ) : ℝ) ^ (1 / ((6 : ℕ) : ℝ))) ^ (i : ℕ) :=
  existsUnique_radical_expansion_coeffs ⟨2, 3, Nat.prime_two, Nat.prime_three, by decide,
    by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by simpa using irreducible_X_pow_six_sub_two) n

-- Uniqueness: the only integer coordinates of `1 + 2 ^ (1 / 6)` are `(1, 1, 0, 0, 0, 0)`.
example (a : Fin 6 → ℤ)
    (ha : 1 + (2 : ℝ) ^ (1 / 6 : ℝ) =
      ∑ i : Fin 6, (a i : ℝ) * ((2 : ℝ) ^ (1 / 6 : ℝ)) ^ (i : ℕ)) :
    a = ![1, 1, 0, 0, 0, 0] := by
  have h := existsUnique_radical_expansion_coeffs (N := 6) (u := 1) (v := 2)
    ⟨2, 3, Nat.prime_two, Nat.prime_three, by decide, by decide, by decide⟩ (by decide)
    (by decide) (by decide) (by simpa using irreducible_X_pow_six_sub_two) 1
  refine h.unique (by simpa using ha) ?_
  simp [Fin.sum_univ_succ]

end MetaMathlibExt.ExistsUniqueRadicalExpansionCoeffsTest
