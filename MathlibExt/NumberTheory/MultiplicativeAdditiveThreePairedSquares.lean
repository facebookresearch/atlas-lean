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
# Multiplicative functions additive on three sums of two positive squares

We prove that such a function fixes 2, 3 and 5 whenever its value at 2 is nonzero.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Small values of a multiplicative function 3-additive on sums of two squares.** Let
$E_2 = \{a^2 + b^2 : a, b \ge 1\}$ be the set of sums of two squares of positive integers. If $f$
is a complex-valued multiplicative function with $f(2) \ne 0$ such that
$f(A_1 + A_2 + A_3) = f(A_1) + f(A_2) + f(A_3)$ for all $A_1, A_2, A_3 \in E_2$, then $f(2) = 2$,
$f(3) = 3$ and $f(5) = 5$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 2 (`integers-2026-A121-lem-2`). -/
public theorem multiplicative_three_additive_two_squares_base (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ A : Fin 3 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
      f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) :
    f 2 = 2 ∧ f 3 = 3 ∧ f 5 = 5 := by
  let E (n : ℕ) := ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2
  have e2 : E 2 := ⟨1, 1, by decide, by decide, rfl⟩
  have e5 : E 5 := ⟨1, 2, by decide, by decide, rfl⟩
  have e8 : E 8 := ⟨2, 2, by decide, by decide, rfl⟩
  have e10 : E 10 := ⟨1, 3, by decide, by decide, rfl⟩
  have e20 : E 20 := ⟨2, 4, by decide, by decide, rfl⟩
  have add_three {a b c : ℕ} (ha : E a) (hb : E b) (hc : E c) :
      f (a + b + c) = f a + f b + f c := by
    simpa only [Fin.sum_univ_three] using! hadd ![a, b, c] (by
      intro i
      fin_cases i <;> assumption)
  have v3 : f 3 = 3 := by
    have eq6 : f 2 * f 3 = f 2 + f 2 + f 2 :=
      (hf.map_mul_of_coprime (m := 2) (n := 3) rfl).symm.trans (add_three e2 e2 e2)
    apply mul_left_cancel₀ h2
    linear_combination eq6
  -- Compare the two triples for 12, and express f(20) using 20 = 5 + 5 + 10.
  have h8 : f 8 = 2 * f 5 - f 2 := by
    linear_combination add_three e2 e5 e5 - add_three e2 e2 e8
  have h20 : f 20 = 2 * f 5 + f 10 := by linear_combination add_three e5 e5 e10
  -- Both 5 + 5 + 20 and 10 + 10 + 10 equal 30.
  have h10 : f 10 = 2 * f 5 := by
    linear_combination (add_three e5 e5 e20 - add_three e10 e10 e10 + h20) / 2
  -- At 24, the triples (2, 2, 20) and (8, 8, 8) now relate f(2) and f(5).
  have ratio : 5 * f 2 = 2 * f 5 := by
    linear_combination add_three e8 e8 e8 - add_three e2 e2 e20 + 3 * h8 - h20 - h10
  have v5 : f 5 = 5 := by
    apply mul_left_cancel₀ h2
    linear_combination -(hf.map_mul_of_coprime (m := 2) (n := 5) rfl) + h10 - ratio
  refine ⟨?_, v3, v5⟩
  rw [v5] at ratio
  linear_combination ratio / 5

end MetaMathlibExt
