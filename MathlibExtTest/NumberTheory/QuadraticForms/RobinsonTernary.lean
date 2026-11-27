/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.RobinsonTernary
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Robinson's lemmas on ternary quadratic forms
-/

@[expose] public section

namespace RobinsonTernaryTest

open Rat.Robinson

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Lemma 3 with the source's binders. -/
example (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (M : ℚ) :
    (∃ X Y Z : ℚ, 2 + p * M ^ 2 + p * Z ^ 2 = X ^ 2 + Y ^ 2) ↔ Odd M.den ∧ M.den.Coprime p :=
  lemma_three hp M

/-- Lemma 4 with the source's binders. -/
example (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1) (hq : q ≠ 2)
    (hqp : legendreSym p q = -1) (M : ℚ) :
    (∃ X Y Z : ℚ, 2 + p * q * M ^ 2 + p * Z ^ 2 = X ^ 2 + q * Y ^ 2) ↔
      M.den.Coprime p ∧ M.den.Coprime q :=
  lemma_four hp hq hqp M

/-- Lemma 3 for `p = 3`: the denominator `2` of `1 / 2` is even, so
`2 + 3 (1 / 2) ^ 2 + 3 Z ^ 2 = X ^ 2 + Y ^ 2` has no rational solution. -/
example : ¬∃ X Y Z : ℚ, 2 + 3 * (1 / 2) ^ 2 + 3 * Z ^ 2 = X ^ 2 + Y ^ 2 := by
  have h := lemma_three (p := 3) (by norm_num) (1 / 2)
  push_cast at h
  rw [h]
  have : (1 / 2 : ℚ).den = 2 := by simp [one_div]
  rw [this]
  decide

/-- Lemma 3 for `p = 3`: the denominator `5` of `1 / 5` is odd and prime to `3`, so
`2 + 3 (1 / 5) ^ 2 + 3 Z ^ 2 = X ^ 2 + Y ^ 2` has a rational solution. -/
example : ∃ X Y Z : ℚ, 2 + 3 * (1 / 5) ^ 2 + 3 * Z ^ 2 = X ^ 2 + Y ^ 2 := by
  have h := lemma_three (p := 3) (by norm_num) (1 / 5)
  push_cast at h
  rw [h]
  have : (1 / 5 : ℚ).den = 5 := by simp [one_div]
  rw [this]
  decide

/-- `3` is a quadratic non-residue modulo `5`. -/
private theorem legendreSym_five_three : legendreSym 5 3 = -1 := by
  rw [legendreSym.eq_neg_one_iff]
  decide

/-- Lemma 4 for `p = 5` and `q = 3`: the denominator `7` of `1 / 7` is prime to `5` and `3`, so
`2 + 15 (1 / 7) ^ 2 + 5 Z ^ 2 = X ^ 2 + 3 Y ^ 2` has a rational solution. -/
example : ∃ X Y Z : ℚ, 2 + 5 * 3 * (1 / 7) ^ 2 + 5 * Z ^ 2 = X ^ 2 + 3 * Y ^ 2 := by
  have h := lemma_four (p := 5) (q := 3) (by norm_num) (by norm_num)
    (by exact_mod_cast legendreSym_five_three) (1 / 7)
  push_cast at h
  rw [h]
  have : (1 / 7 : ℚ).den = 7 := by simp [one_div]
  rw [this]
  decide

/-- Lemma 4 for `p = 5` and `q = 3`: the denominator `3` of `1 / 3` is divisible by `q`, so
`2 + 15 (1 / 3) ^ 2 + 5 Z ^ 2 = X ^ 2 + 3 Y ^ 2` has no rational solution. -/
example : ¬∃ X Y Z : ℚ, 2 + 5 * 3 * (1 / 3) ^ 2 + 5 * Z ^ 2 = X ^ 2 + 3 * Y ^ 2 := by
  have h := lemma_four (p := 5) (q := 3) (by norm_num) (by norm_num)
    (by exact_mod_cast legendreSym_five_three) (1 / 3)
  push_cast at h
  rw [h]
  have : (1 / 3 : ℚ).den = 3 := by simp [one_div]
  rw [this]
  decide

/-- Lemma 1, "only if" half, for `p = 3`: `3 = 3 · 1 · 1 ^ 2` with `(1 / 3) = 1`, so
`X ^ 2 + Y ^ 2 - 3 Z ^ 2` does not represent `3`. -/
example : ¬∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - 3 * Z ^ 2 = 3 := by
  intro h
  have h' := lemma_one_only_if (p := 3) (M := 3) (by norm_num) (by norm_num) (by exact_mod_cast h)
  exact h'.1 ⟨1, 1, by norm_num, by simp⟩

/-- Lemma 1, "only if" half, for `p = 3` at `2`: `-5 ≡ 3 (mod 8)`, so
`X ^ 2 + Y ^ 2 - 3 Z ^ 2` does not represent `-5`. -/
example : ¬∃ X Y Z : ℚ, X ^ 2 + Y ^ 2 - 3 * Z ^ 2 = -5 := by
  intro h
  have h' := lemma_one_only_if (p := 3) (M := -5) (by norm_num) (by norm_num) (by exact_mod_cast h)
  exact h'.2 ⟨-5, 1, by norm_num, by decide⟩

/-- The representation theorem in a case with `m ≡ 2 (mod 4)`: `X ^ 2 + 3 Y ^ 2 - 7 Z ^ 2`
represents `10`. -/
example : ∃ X Y Z : ℚ, X ^ 2 + 3 * Y ^ 2 - 7 * Z ^ 2 = 10 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := exists_sq_add_mul_sq_sub_mul_sq_eq (a := 3) (p := 7) (m := 10) (by norm_num)
    (Nat.prime_three.prime.squarefree) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by norm_num))
  exact_mod_cast h

end RobinsonTernaryTest
