/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.PellBrousseauOdd
import Mathlib.Tactic.NormNum

/-! # Tests for the odd-step Pell Brousseau sum -/

open MetaMathlibExt

example (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasV ⟨2, -1, by decide⟩ m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * pellNumber (m * i) =
      brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p n * pellNumber (m * (n + 1)) +
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p (n + 1) * pellNumber (m * n) -
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p 0 * pellNumber m :=
  pell_brousseau_sum_mul_odd (m := m) (hm := hm) (n := n) (p := p)

-- The empty sum has no i = 0 term, even at power zero.
example (m : ℕ) (hm : Odd m) :
    (lucasV ⟨2, -1, by decide⟩ m : ℚ) *
      ∑ i ∈ Finset.Icc (1 : ℕ) 0, (i : ℚ) ^ 0 * pellNumber (m * i) = 0 := by
  have h := pell_brousseau_sum_mul_odd (m := m) (hm := hm) (n := 0) (p := 0)
  simpa only [brousseauCoeff_zero, Nat.zero_add, Nat.mul_one, Nat.mul_zero,
    pellNumber, Nat.cast_zero, one_mul, add_zero, sub_self] using h

-- Q₃ = 14 and the two Pell terms in the sum are P₃ = 5 and P₆ = 70.
example : (14 : ℚ) * ∑ i ∈ Finset.Icc (1 : ℕ) 2, (i : ℚ) ^ 0 * pellNumber (3 * i) = 1050 := by
  have h := pell_brousseau_sum_mul_odd (m := 3) (hm := by decide) (n := 2) (p := 0)
  norm_num [brousseauCoeff_zero, lucasV, pellNumber] at h ⊢
  exact h

example : (14 : ℚ) * ∑ i ∈ Finset.Icc (1 : ℕ) 2, (i : ℚ) ^ 1 * pellNumber (3 * i) = 2030 := by
  have h := pell_brousseau_sum_mul_odd (m := 3) (hm := by decide) (n := 2) (p := 1)
  norm_num [brousseauCoeff_one, lucasV, pellNumber] at h ⊢
  exact h
