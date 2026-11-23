/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Additive uniqueness of generalized nonagonal numbers

Two decompositions each of 90 and 94 determine the values at 6 and 9.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- A multiplicative arithmetic function additive on pairs of positive generalized nonagonal
numbers fixes every integer from 1 through 11.

The ATLAS article *Nonagonal additive uniqueness: the values up to 11* attributes this result to
Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for Multiplicative
Functions*, INTEGERS 25 (2025), Article A99, Lemma 1.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Lemma 1
(`integers-2025-A99-lem-1`). -/
public theorem multiplicative_nonagonal_additive_eq_self_of_le_eleven
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 11 → f n = n := by
  let N (a : ℕ) := 0 < a ∧ ∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)
  have add {a b : ℕ} (ha : N a) (hb : N b) : f (a + b) = f a + f b :=
    hadd a b ha.1 hb.1 ha.2 hb.2
  have n1 : N 1 := ⟨by decide, 1, by decide⟩
  have n6 : N 6 := ⟨by decide, -1, by decide⟩
  have n9 : N 9 := ⟨by decide, 2, by decide⟩
  have n19 : N 19 := ⟨by decide, -2, by decide⟩
  have n24 : N 24 := ⟨by decide, 3, by decide⟩
  have n39 : N 39 := ⟨by decide, -3, by decide⟩
  have n46 : N 46 := ⟨by decide, 4, by decide⟩
  have n66 : N 66 := ⟨by decide, -4, by decide⟩
  have n75 : N 75 := ⟨by decide, 5, by decide⟩
  have h1 := hf.map_one
  have h2 : f 2 = 2 := by linear_combination add n1 n1 + 2 * h1
  have double (a : ℕ) (ha : Nat.Coprime 2 a) : f (2 * a) = 2 * f a := by
    rw [hf.map_mul_of_coprime ha, h2]
  -- Express the summands in terms of f 6 and f 9 by comparing representations of
  -- 30, 25, 48 and 66, respectively.
  have h24 : f 24 = f 6 + 2 * f 9 := by
    linear_combination double 15 (by decide) + 2 * add n6 n9 - add n6 n24
  have h19 : f 19 = 1 + 2 * f 9 := by
    linear_combination add n1 n24 - add n6 n19 + h1 + h24
  have h39 : f 39 = 2 * f 6 + 3 * f 9 := by
    linear_combination add n24 n24 - add n9 n39 + 2 * h24
  have h66 : f 66 = 2 * f 6 + 6 * f 9 := by
    linear_combination double 33 (by decide) + 2 * add n9 n24 + 2 * h24
  -- 90 = 24 + 66 = 2(6 + 39) gives the first linear relation.
  have rel90 : 3 * f 6 = 2 * f 9 := by
    linear_combination add n24 n66 - double 45 (by decide) - 2 * add n6 n39 +
      h24 + h66 - 2 * h39
  -- 85 = 19 + 66 = 39 + 46 and 75 = 9 + 66 supply the summands for the second.
  have h46 : f 46 = 1 + 5 * f 9 := by
    linear_combination add n19 n66 - add n39 n46 + h19 + h66 - h39
  have h75 : f 75 = 2 * f 6 + 7 * f 9 := by
    linear_combination add n9 n66 + h66
  -- 94 = 19 + 75 = 2(1 + 46).
  have rel94 : 2 * f 6 = 3 + f 9 := by
    linear_combination double 47 (by decide) + 2 * add n1 n46 - add n19 n75 -
      h19 - h75 + 2 * h1 + 2 * h46
  have h6 : f 6 = 6 := by linear_combination 2 * rel94 - rel90
  have h9 : f 9 = 9 := by linear_combination 3 * rel94 - 2 * rel90
  -- Recover the other values from nonagonal sums and coprime products.
  have h3 : f 3 = 3 := by linear_combination (h6 - double 3 (by decide)) / 2
  have triple (a : ℕ) (ha : Nat.Coprime 3 a) : f (3 * a) = 3 * f a := by
    rw [hf.map_mul_of_coprime ha, h3]
  have h4 : f 4 = 4 := by
    linear_combination (add n6 n6 + 2 * h6 - triple 4 (by decide)) / 3
  have h10 : f 10 = 10 := by linear_combination add n1 n9 + h1 + h9
  have h5 : f 5 = 5 := by linear_combination (h10 - double 5 (by decide)) / 2
  have h7 : f 7 = 7 := by linear_combination add n1 n6 + h1 + h6
  norm_num [h6, h9] at h24
  have h8 : f 8 = 8 := by linear_combination (h24 - triple 8 (by decide)) / 3
  have h11 : f 11 = 11 := by
    linear_combination (add n9 n24 + h9 + h24 - triple 11 (by decide)) / 3
  intro n hn hle
  interval_cases n <;> norm_num1 <;> assumption

end MetaMathlibExt
