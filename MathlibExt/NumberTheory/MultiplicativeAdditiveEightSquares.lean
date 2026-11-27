/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
import all MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on eight positive squares

A multiplicative function that is additive on four sums of two positive squares and is nonzero
at two fixes every positive integer. We follow the strong induction in Jewel Mahajan,
*Multiplicative Functions Additive on Partitions of 2k Nonzero Squares*
(https://arxiv.org/abs/2606.29507).
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace multiplicative_additive_eight_squares_eq_id

private def IsPair (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2

private theorem small_values {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (add : ∀ A : Fin 4 → ℕ, (∀ i, IsPair (A i)) → f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) (n : ℕ) (hn : 0 < n) (hlt : n < 22) : f n = n := by
  have base := multiplicative_four_additive_two_squares_base f hf add h2
  let Good (m : ℕ) := IsPair m ∧ f m = m
  have e2 : Good 2 := ⟨⟨1, 1, by decide, by decide, rfl⟩, base 2 (by decide)⟩
  have e5 : Good 5 := ⟨⟨1, 2, by decide, by decide, rfl⟩, base 5 (by decide)⟩
  have e8 : Good 8 := ⟨⟨2, 2, by decide, by decide, rfl⟩, base 8 (by decide)⟩
  have e10 : Good 10 := ⟨⟨1, 3, by decide, by decide, rfl⟩, base 10 (by decide)⟩
  have four {a b c d : ℕ} (ha : Good a) (hb : Good b) (hc : Good c) (hd : Good d) :
      f (a + b + c + d) = ↑(a + b + c + d) := by
    have eq : f (a + b + c + d) = f a + f b + f c + f d := by
      simpa only [Fin.sum_univ_four] using! add ![a, b, c, d] (by
        intro i
        fin_cases i
        exacts [ha.1, hb.1, hc.1, hd.1])
    simp only [eq, ha.2, hb.2, hc.2, hd.2, Nat.cast_add]
  have prod (a b : ℕ) (hab : a.Coprime b) (ha : f a = a) (hb : f b = b) :
      f (a * b) = ↑(a * b) := by rw [hf.map_mul_of_coprime hab, ha, hb, Nat.cast_mul]
  -- The four-pair decompositions of 36 and 26 determine the missing factors 9 and 13.
  have v9 : f 9 = 9 := by
    have eq := four e8 e8 e10 e10
    change f (4 * 9) = 36 at eq
    rw [hf.map_mul_of_coprime (by decide : Nat.Coprime 4 9), base 4 (by decide)] at eq
    linear_combination eq / 4
  have v13 : f 13 = 13 := by
    have eq := four e2 e8 e8 e8
    change f (2 * 13) = 26 at eq
    rw [hf.map_mul_of_coprime (by decide : Nat.Coprime 2 13), e2.2] at eq
    linear_combination eq / 2
  interval_cases n <;> try first | exact base _ (by decide) | assumption
  · simpa only [Nat.cast_one] using hf.1
  · simpa only using four e2 e2 e2 e5
  · exact prod 3 4 (by decide) (base 3 (by decide)) (base 4 (by decide))
  · simpa only using four e2 e2 e2 e8
  · exact prod 3 5 (by decide) (base 3 (by decide)) e5.2
  · simpa only using four e2 e2 e2 e10
  · simpa only using four e2 e2 e5 e8
  · exact prod 2 9 (by decide) e2.2 v9
  · simpa only using four e2 e2 e5 e10
  · simpa only using four e5 e5 e5 e5
  · exact prod 3 7 (by decide) (base 3 (by decide)) (base 7 (by decide))

end multiplicative_additive_eight_squares_eq_id

open multiplicative_additive_eight_squares_eq_id
open multiplicative_additive_paired_squares_eq_id_of_ne_zero (eight_squares weight) in
/-- **Multiplicative functions additive on eight paired squares and nonzero at $2$ are the
identity.** Let $f$ be a complex-valued multiplicative function with $f(2) \ne 0$ such that
$$f\Big(\sum_{j=1}^{4} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{4} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, \dots, x_4, y_1, \dots, y_4$. Then $f(n) = n$ for every positive
integer $n$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 4 (`integers-2026-A121-thm-4`). -/
public theorem multiplicative_additive_eight_squares_eq_id (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 4 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  have add (A : Fin 4 → ℕ) (hA : ∀ i, IsPair (A i)) : f (∑ i, A i) = ∑ i, f (A i) := by
    choose x y hx hy heq using hA
    simpa only [heq] using hadd x y hx hy
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hlt : n < 22
    · exact small_values hf add h2 n hn hlt
    obtain ⟨A, hA⟩ := eight_squares (Nat.le_of_not_gt hlt)
    have pos (i : Fin 4) : 0 < weight (A i) :=
      Nat.add_pos_left (pow_pos (A i).1.2 2) _
    have lt (i : Fin 4) : weight (A i) < n := by
      obtain ⟨j, hji⟩ := exists_ne i
      rw [← hA]
      exact Finset.single_lt_sum hji (Finset.mem_univ _) (Finset.mem_univ _) (pos j)
        fun k _ _ ↦ (pos k).le
    calc
      f n = ∑ i, f (weight (A i)) := hA ▸ hadd _ _ (fun i ↦ (A i).1.2) (fun i ↦ (A i).2.2)
      _ = ∑ i, (weight (A i) : ℂ) := Finset.sum_congr rfl fun i _ ↦ ih _ (lt i) (pos i)
      _ = n := by rw [← Nat.cast_sum, hA]

end MetaMathlibExt
