/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.FiniteDividendDiscount
import Mathlib.Tactic

/-!
# Tests for finite dividend-discount identity

Tests for the finite dividend-discount identity: concrete `n = 2` examples at
`r = 1/10` (`P 0 = 2410/121`) and `r = 0` (`P 0 = 15`), and the generic `n = 1` corollary.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.FiniteDividendDiscount

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.FiniteDividendDiscount

def testD : ℕ → ℝ := fun t => if t = 1 then (11:ℝ) else if t = 2 then 12 else 0

noncomputable def testP : ℕ → ℝ :=
  fun t => if t = 0 then (2410/121:ℝ) else if t = 1 then 120/11 else 0

theorem testP_recursion :
    ∀ t, testP t = (testD (t + 1) + testP (t + 1)) / (1 + (1/10:ℝ)) := by
  intro t
  by_cases h0 : t = 0
  · subst h0
    norm_num [testD, testP]
  · by_cases h1 : t = 1
    · subst h1
      norm_num [testD, testP]
    · have ht1_ne2 : t + 1 ≠ 2 := by omega
      simp [testD, testP, h0, h1, ht1_ne2]

theorem testP_finite_identity :
    testP 0 = presentValue (discountFactor (1/10)) (Finset.Icc 1 2) testD +
      discountFactor (1/10) 2 * testP 2 :=
  finiteDividendDiscount (by norm_num) testP_recursion 2

theorem testP_two : testP 2 = 0 := by norm_num [testP]

theorem testP_value : testP 0 = 2410/121 := by
  rw [testP_finite_identity, testP_two]
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := rfl
  rw [hIcc]
  simp only [presentValue, Finset.sum_pair (show (1:ℕ) ≠ 2 by norm_num)]
  norm_num [discountFactor, testD]

def testD0 : ℕ → ℝ := fun t => if t = 1 then (5:ℝ) else if t = 2 then 7 else 0

def testP0 : ℕ → ℝ := fun t => if t = 0 then (15:ℝ) else if t = 1 then 10 else 3

theorem testP0_recursion :
    ∀ t, testP0 t = (testD0 (t + 1) + testP0 (t + 1)) / (1 + (0:ℝ)) := by
  intro t
  by_cases h0 : t = 0
  · subst h0
    norm_num [testD0, testP0]
  · by_cases h1 : t = 1
    · subst h1
      norm_num [testD0, testP0]
    · have ht1_ne2 : t + 1 ≠ 2 := by omega
      simp [testD0, testP0, h0, h1, ht1_ne2]

theorem testP0_finite_identity :
    testP0 0 = presentValue (discountFactor 0) (Finset.Icc 1 2) testD0 +
      discountFactor 0 2 * testP0 2 :=
  finiteDividendDiscount (by norm_num) testP0_recursion 2

theorem testP0_two : testP0 2 = 3 := by norm_num [testP0]

theorem testP0_value : testP0 0 = 15 := by
  rw [testP0_finite_identity, testP0_two]
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := rfl
  rw [hIcc]
  simp only [presentValue, Finset.sum_pair (show (1:ℕ) ≠ 2 by norm_num)]
  norm_num [discountFactor, testD0]

theorem n1_corollary {r : ℝ} {D P : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hrec : ∀ t, P t = (D (t + 1) + P (t + 1)) / (1 + r)) :
    P 0 = discountFactor r 1 * D 1 + discountFactor r 1 * P 1 := by
  have h := finiteDividendDiscount hr hrec 1
  rw [Finset.Icc_self] at h
  simp only [presentValue, Finset.sum_singleton] at h
  exact h


end MathlibExtTest.Economics.Finance.FiniteDividendDiscount
