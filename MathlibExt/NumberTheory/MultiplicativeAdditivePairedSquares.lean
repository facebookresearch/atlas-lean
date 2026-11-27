/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on four sums of two positive squares

The proof follows the four-summand base case in Jewel Mahajan,
*Multiplicative functions additive on partitions of 2k nonzero squares*
(https://arxiv.org/abs/2606.29507).
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Small values of a multiplicative function 4-additive on sums of two squares.** Let
$E_2 = \{a^2 + b^2 : a, b \ge 1\}$ be the set of sums of two squares of positive integers. If $f$
is a complex-valued multiplicative function with $f(2) \ne 0$ such that
$f(A_1 + A_2 + A_3 + A_4) = f(A_1) + f(A_2) + f(A_3) + f(A_4)$ for all $A_1, \dots, A_4 \in E_2$,
then $f(n) = n$ for every $n \in \{2, 3, 4, 5, 6, 7, 8, 10\}$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 3 (`integers-2026-A121-lem-3`). -/
public theorem multiplicative_four_additive_two_squares_base (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ A : Fin 4 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
      f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) :
    ∀ n ∈ ({2, 3, 4, 5, 6, 7, 8, 10} : Finset ℕ), f n = n := by
  let E (n : ℕ) := ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2
  have e2 : E 2 := ⟨1, 1, by decide, by decide, rfl⟩
  have e5 : E 5 := ⟨1, 2, by decide, by decide, rfl⟩
  have e8 : E 8 := ⟨2, 2, by decide, by decide, rfl⟩
  have e10 : E 10 := ⟨1, 3, by decide, by decide, rfl⟩
  have add_four {a b c d : ℕ} (ha : E a) (hb : E b) (hc : E c) (hd : E d) :
      f (a + b + c + d) = f a + f b + f c + f d := by
    simpa only [Fin.sum_univ_four] using! hadd ![a, b, c, d] (by
      intro i
      fin_cases i <;> assumption)
  have h8 : f 8 = 4 * f 2 := by linear_combination add_four e2 e2 e2 e2
  have h10 : f 10 = f 2 * f 5 := hf.map_mul_of_coprime (m := 2) (n := 5) rfl
  -- Comparing two decompositions of 32 gives 16 f(2) = f(2) + 3 f(2) f(5).
  have v5 : f 5 = 5 := by
    have eq32 := add_four e2 e10 e10 e10
    have eq32' := add_four e8 e8 e8 e8
    rw [h10] at eq32
    rw [h8] at eq32'
    apply mul_left_cancel₀ h2
    linear_combination (eq32' - eq32) / 3
  -- Now 14 = 2 + 2 + 2 + 8 = 2 + 2 + 5 + 5 determines f(2).
  have h14 : f 14 = 7 * f 2 := by linear_combination add_four e2 e2 e2 e8 + h8
  have v2 : f 2 = 2 := by
    have eq14 := add_four e2 e2 e5 e5
    change f 14 = _ at eq14
    rw [h14, v5] at eq14
    linear_combination eq14 / 5
  rw [v2] at h8 h14
  rw [v2, v5] at h10
  norm_num at h8 h10 h14
  have v3 : f 3 = 3 := by
    have eq24 := add_four e2 e2 e10 e10
    change f (3 * 8) = _ at eq24
    rw [hf.map_mul_of_coprime rfl, h8, v2, h10] at eq24
    linear_combination eq24 / 8
  have v4 : f 4 = 4 := by
    have eq20 := add_four e5 e5 e5 e5
    change f (4 * 5) = _ at eq20
    rw [hf.map_mul_of_coprime rfl, v5] at eq20
    linear_combination eq20 / 5
  have v6 : f 6 = 6 := by
    change f (2 * 3) = 6
    rw [hf.map_mul_of_coprime rfl, v2, v3]
    norm_num
  have v7 : f 7 = 7 := by
    have eq14 := (hf.map_mul_of_coprime (m := 2) (n := 7) rfl).symm.trans h14
    rw [v2] at eq14
    linear_combination eq14 / 2
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

end MetaMathlibExt
