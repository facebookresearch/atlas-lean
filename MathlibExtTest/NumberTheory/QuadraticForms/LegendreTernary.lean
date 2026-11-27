/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.LegendreTernary
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Legendre's theorem on $a x^2 + b y^2 + c z^2 = 0$
-/

@[expose] public section

namespace LegendreTernaryTest

/-- An integer whose absolute value is a prime is square free. -/
private theorem squarefree_of_natAbs_prime {n : ℤ} (h : Nat.Prime n.natAbs) : Squarefree n :=
  (Int.prime_iff_natAbs_prime.mpr h).squarefree

/-- The theorem with the source's binders: `(i) -ab R c`, `(ii) -ac R b` and `(iii) -bc R a`,
where `m R n` means that `x ^ 2 ≡ m [ZMOD n]` for some integer `x`. -/
example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (ha' : Squarefree a)
    (hb' : Squarefree b) (hc' : Squarefree c) (hab : IsCoprime a b) (hbc : IsCoprime b c)
    (hac : IsCoprime a c) (hpos : ¬(0 < a ∧ 0 < b ∧ 0 < c)) (hneg : ¬(a < 0 ∧ b < 0 ∧ c < 0)) :
    (∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      (∃ x : ℤ, x ^ 2 ≡ -(a * b) [ZMOD c]) ∧ (∃ x : ℤ, x ^ 2 ≡ -(a * c) [ZMOD b]) ∧
        ∃ x : ℤ, x ^ 2 ≡ -(b * c) [ZMOD a] :=
  Int.exists_ternary_eq_zero_iff ha hb hc ha' hb' hc' hab hbc hac hpos hneg

/-- `-1` is not a square modulo `-3`. -/
private theorem not_sq_modEq_neg_one : ¬∃ x : ℤ, x ^ 2 ≡ -(1 * 1) [ZMOD -3] := by
  rintro ⟨x, hx⟩
  rw [Int.modEq_neg] at hx
  have h := (ZMod.intCast_eq_intCast_iff (x ^ 2) (-(1 * 1)) 3).mpr hx
  push_cast at h
  generalize (x : ZMod 3) = u at h
  revert u
  decide

/-- Necessity: `x ^ 2 + y ^ 2 = 3 z ^ 2` has only the zero solution in integers. -/
example : ¬∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ 1 * x ^ 2 + 1 * y ^ 2 + -3 * z ^ 2 = 0 := by
  rw [Int.exists_ternary_eq_zero_iff one_ne_zero one_ne_zero (by norm_num) squarefree_one
    squarefree_one (squarefree_of_natAbs_prime (by norm_num)) isCoprime_one_left
    isCoprime_one_left isCoprime_one_left (by norm_num) (by norm_num)]
  exact fun h => not_sq_modEq_neg_one h.1

/-- Sufficiency: the three conditions give a nontrivial solution of
`x ^ 2 + 2 y ^ 2 - 3 z ^ 2 = 0`. -/
example : ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ 1 * x ^ 2 + 2 * y ^ 2 + -3 * z ^ 2 = 0 := by
  rw [Int.exists_ternary_eq_zero_iff one_ne_zero two_ne_zero (by norm_num) squarefree_one
    (squarefree_of_natAbs_prime (by norm_num)) (squarefree_of_natAbs_prime (by norm_num))
    isCoprime_one_left (by rw [Int.isCoprime_iff_gcd_eq_one]; rfl) isCoprime_one_left
    (by norm_num) (by norm_num)]
  exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩

/-- Sufficiency when `a = b = 1`: as `-1` is a square modulo `5`, `x ^ 2 + y ^ 2 = 5 z ^ 2` has a
nontrivial solution. -/
example : ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ 1 * x ^ 2 + 1 * y ^ 2 + -5 * z ^ 2 = 0 := by
  rw [Int.exists_ternary_eq_zero_iff one_ne_zero one_ne_zero (by norm_num) squarefree_one
    squarefree_one (squarefree_of_natAbs_prime (by norm_num)) isCoprime_one_left
    isCoprime_one_left isCoprime_one_left (by norm_num) (by norm_num)]
  exact ⟨⟨2, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- A negative leading coefficient: `-7 x ^ 2 + 2 y ^ 2 + 5 z ^ 2 = 0` has the solution
`(1, 1, 1)`, so the three conditions hold. -/
example : (∃ x : ℤ, x ^ 2 ≡ -(-7 * 2) [ZMOD 5]) ∧ (∃ x : ℤ, x ^ 2 ≡ -(-7 * 5) [ZMOD 2]) ∧
    ∃ x : ℤ, x ^ 2 ≡ -(2 * 5) [ZMOD -7] := by
  rw [← Int.exists_ternary_eq_zero_iff (by norm_num) two_ne_zero (by norm_num)
    (squarefree_of_natAbs_prime (by norm_num)) (squarefree_of_natAbs_prime (by norm_num))
    (squarefree_of_natAbs_prime (by norm_num)) (by rw [Int.isCoprime_iff_gcd_eq_one]; rfl)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; rfl) (by rw [Int.isCoprime_iff_gcd_eq_one]; rfl)
    (by norm_num) (by norm_num)]
  exact ⟨1, 1, 1, by simp, by norm_num⟩

end LegendreTernaryTest
