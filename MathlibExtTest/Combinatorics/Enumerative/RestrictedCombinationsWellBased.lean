/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.RestrictedCombinationsWellBased

open Finset MetaMathlibExt PowerSeries

local notation "Y" => (Polynomial.X : Polynomial ℤ)
local notation "x" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
local notation "y" => (PowerSeries.C Y)

private noncomputable def series (Q : Finset ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => ∑ k ∈ range (n + 1), (restrictedCombinationCount Q n k : Polynomial ℤ) * Y ^ k

private noncomputable def numerator (Q : Finset ℕ) : PowerSeries (Polynomial ℤ) :=
  1 + ∑ q ∈ Q, x ^ q * y

private noncomputable def denominator (Q : Finset ℕ) : PowerSeries (Polynomial ℤ) :=
  (1 - x) * numerator Q - x * y

-- Independently count all subset sizes on the empty board and on a small unrestricted board.
example : (List.range 1).map (restrictedCombinationCount ∅ 0) = [1] ∧
    (List.range 5).map (restrictedCombinationCount ∅ 4) = [1, 4, 6, 4, 1] := by
  decide

-- When 1 is forbidden, the only two-element subset of {1, 2, 3} is {1, 3}.
example : (List.range 4).map (restrictedCombinationCount {1} 3) = [1, 3, 1, 0] := by decide

-- The empty board gives a constant term of one in the unrestricted product.
example : coeff 0 (series ∅ * denominator ∅) = 1 := by
  have h : restrictedCombinationCount ∅ 0 0 = 1 := by decide
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply (series ∅)]
  simp [series, denominator, numerator, h]

-- Check the additive-gap API independently for the non-interval set: the allowed gaps
-- 2 and 2 give 4, and 4 is not forbidden (even though both 1 and 3 are).
example : (2 : ℕ) ∉ ({1, 3} : Finset ℕ) ∧ 2 + 2 ∉ ({1, 3} : Finset ℕ) := by decide

-- Independently compare both sides of the weighted enumeration with a numeral.
example : (∑ k ∈ range 4, restrictedCombinationCount {1} 3 k * (k + 1)) = 10 ∧
    (∑ s ∈ (Icc 1 3).powerset.filter
      (fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ ({1} : Finset ℕ)), (s.card + 1)) = 10 := by
  decide

private def counts13 (n k : ℕ) : ℕ :=
  (([[1], [1, 1], [1, 2], [1, 3, 1], [1, 4, 2], [1, 5, 4, 1]] :
    List (List ℕ))[n]?.getD [])[k]?.getD 0

-- Evaluate the actual subset enumerator, independently of the generating-function theorem.
private theorem counts13_correct : ∀ n k : Fin 6,
    restrictedCombinationCount {1, 3} n k = counts13 n k := by decide

private theorem coeff_series13 {n : ℕ} (hn : n < 6) :
    coeff n (series {1, 3}) = ∑ k ∈ range (n + 1), (counts13 n k : Polynomial ℤ) * Y ^ k := by
  rw [series, coeff_mk]
  apply sum_congr rfl
  intro k hk
  rw [counts13_correct ⟨n, hn⟩ ⟨k, (mem_range.mp hk).trans_le hn⟩]

-- Compute in ℤ[y][[x]] directly. The x³ term detects the nonconstant numerator;
-- the x⁵ term includes the cubic count from the subset {1, 3, 5}.
example : coeff 3 (series {1, 3} * denominator {1, 3}) = coeff 3 (numerator {1, 3}) ∧
    coeff 5 (series {1, 3} * denominator {1, 3}) = coeff 5 (numerator {1, 3}) := by
  have hden : denominator {1, 3} = 1 - x - (x ^ 2 * y) + x ^ 3 * y - x ^ 4 * y := by
    simp only [denominator, numerator, sum_insert (show (1 : ℕ) ∉ ({3} : Finset ℕ) by decide),
      sum_singleton]
    ring
  rw [hden]
  constructor <;>
    simp only [mul_sub, mul_add, mul_one, map_add, map_sub, ← mul_assoc, coeff_mul_C,
      coeff_succ_mul_X, coeff_mul_X_pow'] <;>
    norm_num [numerator, sum_insert, coeff_mul_C, coeff_one, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X,
      coeff_series13 (n := 0) (by decide), coeff_series13 (n := 1) (by decide),
      coeff_series13 (n := 2) (by decide), coeff_series13 (n := 3) (by decide),
      coeff_series13 (n := 4) (by decide), coeff_series13 (n := 5) (by decide),
      sum_range_succ, counts13] <;> ring

-- A public client with a well-based set that is not an initial interval.
example : series {1, 3} * denominator {1, 3} = numerator {1, 3} := by
  have h : IsWellBased ({1, 3} : Finset ℕ) := by
    rw [← subwordShiftSet_1010]
    exact isWellBased_subwordShiftSet 0b1010 4 (by decide)
  exact restrictedCombination_bivariate_genFun_of_isWellBased {1, 3} (by decide) h
