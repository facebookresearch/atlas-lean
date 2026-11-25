/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Internal shift identity for Brousseau coefficients -/

namespace MetaMathlibExt

open Finset

namespace BrousseauSum

-- Expand the shifted polynomial and group terms by the total order of the shift.
private lemma coeff_add (k : ℚ) (p : ℕ) (x y : ℚ) :
    brousseauCoeff k p (x + y) =
      ∑ s ∈ range (p + 1), brousseauCoeff k s y * (p.choose s : ℚ) * x ^ (p - s) := by
  let term (r d : ℕ) := (-1 : ℚ) ^ r * brousseauA k r * (p.choose r : ℚ) *
    (y ^ d * x ^ (p - r - d) * ((p - r).choose d : ℚ))
  calc
    _ = ∑ r ∈ range (p + 1), ∑ d ∈ range (p + 1 - r), term r d := by
      rw [brousseauCoeff]
      refine sum_congr rfl fun r hr ↦ ?_
      have hr' : r ≤ p := Nat.le_of_lt_succ (mem_range.mp hr)
      rw [add_comm x y, add_pow, mul_sum, show p + 1 - r = p - r + 1 by omega]
    _ = ∑ s ∈ range (p + 1), ∑ r ∈ range (s + 1), term r (s - r) :=
      (sum_range_diag_flip _ _).symm
    _ = _ := by
      refine sum_congr rfl fun s hs ↦ ?_
      have hs' : s ≤ p := Nat.le_of_lt_succ (mem_range.mp hs)
      rw [brousseauCoeff, sum_mul, sum_mul]
      refine sum_congr rfl fun r hr ↦ ?_
      have hr' : r ≤ s := Nat.le_of_lt_succ (mem_range.mp hr)
      have hchoose : (p.choose s : ℚ) * (s.choose r : ℚ) =
          (p.choose r : ℚ) * ((p - r).choose (s - r) : ℚ) := by
        exact_mod_cast Nat.choose_mul (n := p) hr'
      simp only [term, show p - r - (s - r) = p - s by omega]
      linear_combination -((-1 : ℚ) ^ r * brousseauA k r * y ^ (s - r) *
        x ^ (p - s)) * hchoose

-- At zero only the constant term survives. The difference at ±1 selects odd binomial terms.
private lemma coeff_at_shifts (k : ℚ) (hk : k ≠ 0) (p : ℕ) :
    k * brousseauCoeff k (p + 1) 0 +
      brousseauCoeff k (p + 1) 1 - brousseauCoeff k (p + 1) (-1) = 0 := by
  have hzero : brousseauCoeff k (p + 1) 0 = (-1 : ℚ) ^ (p + 1) * brousseauA k (p + 1) := by
    rw [brousseauCoeff, sum_range_succ, sum_eq_zero]
    · simp
    · intro r hr
      rw [zero_pow (by have := mem_range.mp hr; omega), mul_zero]
  let a (d : ℕ) := ((p + 1).choose d : ℚ) * brousseauA k (p + 1 - d)
  have hdiff : brousseauCoeff k (p + 1) 1 - brousseauCoeff k (p + 1) (-1) =
      (-1 : ℚ) ^ (p + 1) * ∑ d ∈ range (p + 2), ((-1 : ℚ) ^ d - 1) * a d := by
    rw [brousseauCoeff, brousseauCoeff, ← sum_sub_distrib, mul_sum, ← sum_flip
      (fun d ↦ (-1 : ℚ) ^ (p + 1) * (((-1 : ℚ) ^ d - 1) * a d))]
    refine sum_congr rfl fun r hr ↦ ?_
    have hr' : r ≤ p + 1 := Nat.le_of_lt_succ (mem_range.mp hr)
    simp only [a, Nat.choose_symm hr', Nat.sub_sub_self hr', one_pow, mul_one]
    have hsplit : (-1 : ℚ) ^ (p + 1) = (-1) ^ r * (-1) ^ (p + 1 - r) := by
      rw [← pow_add, Nat.add_sub_of_le hr']
    rw [hsplit]
    have hsign : (-1 : ℚ) ^ (p + 1 - r) * (-1) ^ (p + 1 - r) = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination -((-1 : ℚ) ^ r * brousseauA k r * ((p + 1).choose r : ℚ)) * hsign
  have hodd : (∑ d ∈ range (p + 2), ((-1 : ℚ) ^ d - 1) * a d) =
      -2 * ∑ j ∈ range ((p + 2) / 2), a (2 * j + 1) := by
    calc
      _ = -2 * ∑ d ∈ (range (p + 2)).filter (fun d ↦ d % 2 = 1), a d := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun d _ ↦ ?_
        rw [neg_one_pow_eq_pow_mod_two]
        rcases Nat.mod_two_eq_zero_or_one d with h | h <;> norm_num [h]
      _ = _ := by
        congr 1
        symm
        apply sum_bij (fun j _ ↦ 2 * j + 1)
        · simp only [mem_range, mem_filter]
          omega
        · intro i _ j _ h
          omega
        · intro d hd
          simp only [mem_filter, mem_range] at hd
          exact ⟨d / 2, mem_range.mpr (by omega), by omega⟩
        · intro j _
          rfl
  have ha : k * brousseauA k (p + 1) = 2 * ∑ j ∈ range ((p + 2) / 2), a (2 * j + 1) := by
    have hindex (j : ℕ) : p + 1 - (2 * j + 1) = p - 2 * j := by omega
    simp only [a, hindex]
    rw [brousseauA.eq_2]
    field_simp
  rw [hzero, add_sub_assoc, hdiff, hodd]
  linear_combination (-1 : ℚ) ^ (p + 1) * ha

public lemma coeff_shift (k : ℚ) (hk : k ≠ 0) (p : ℕ) (x : ℚ) :
    k * brousseauCoeff k p x + brousseauCoeff k p (x + 1) - brousseauCoeff k p (x - 1) =
      k * x ^ p := by
  have hzero := coeff_add k p x 0
  rw [add_zero] at hzero
  rw [hzero, sub_eq_add_neg x 1, coeff_add, coeff_add, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  calc
    _ = ∑ s ∈ range (p + 1), (k * brousseauCoeff k s 0 +
        brousseauCoeff k s 1 - brousseauCoeff k s (-1)) * (p.choose s : ℚ) * x ^ (p - s) := by
      refine sum_congr rfl fun s _ ↦ ?_
      ring
    _ = _ := by
      rw [sum_eq_single 0]
      · simp [brousseauCoeff_zero]
      · intro s _ hs
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
        simp [coeff_at_shifts k hk s]
      · simp

end BrousseauSum

end MetaMathlibExt
