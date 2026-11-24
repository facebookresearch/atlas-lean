/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ArithmeticCoding
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Tests: arithmetic coding
-/

@[expose] public section

namespace MathlibExt.InformationTheory.ArithmeticCoding.Tests

set_option autoImplicit false

open MathlibExt.InformationTheory.ArithmeticCoding
open scoped BigOperators

#print axioms arithCode_interval_subset
#print axioms arithCode_isPrefixFree
#print axioms arithCode_injective

/-- The fair two-symbol assignment `q = (1/2, 1/2)` on `Fin 2`. -/
def fairTwo : Fin 2 → ℚ := fun _ => 1 / 2

/-- For the fair two-symbol assignment, the codewords are `[false, false]`
and `[true, false]`, each of length `⌈log₂ 2⌉ + 1 = 2`. -/
theorem arithCode_fairTwo :
    arithCode fairTwo 0 = [false, false] ∧
      arithCode fairTwo 1 = [true, false] ∧
      (arithCode fairTwo 0).length = 2 ∧ (arithCode fairTwo 1).length = 2 := by
  have hset0 : Finset.univ.filter (fun j : Fin 2 => j.val < (0 : Fin 2).val) = ∅ := by
    decide
  have hset1 : Finset.univ.filter (fun j : Fin 2 => j.val < (1 : Fin 2).val) = {0} := by
    decide
  have hcum0 : cum fairTwo 0 = 0 := by
    simp only [cum]
    show ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j.val < (0 : Fin 2).val), fairTwo j = 0
    rw [hset0, Finset.sum_empty]
  have hcum1 : cum fairTwo 1 = 1 / 2 := by
    simp only [cum]
    show ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j.val < (1 : Fin 2).val), fairTwo j = 1 / 2
    rw [hset1, Finset.sum_singleton]
    rfl
  have hL0 : codeLen fairTwo 0 = 2 := by
    simp only [codeLen, fairTwo]
    show ⌈Real.logb 2 ((((1 / 2 : ℚ)) : ℝ))⁻¹⌉₊ + 1 = 2
    have hinv : ((((1 / 2 : ℚ)) : ℝ))⁻¹ = 2 := by norm_num
    rw [hinv, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Nat.ceil_one]
  have hL1 : codeLen fairTwo 1 = 2 := by
    simp only [codeLen, fairTwo]
    show ⌈Real.logb 2 ((((1 / 2 : ℚ)) : ℝ))⁻¹⌉₊ + 1 = 2
    have hinv : ((((1 / 2 : ℚ)) : ℝ))⁻¹ = 2 := by norm_num
    rw [hinv, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Nat.ceil_one]
  have hI0 : codeInt fairTwo 0 = 0 := by
    simp only [codeInt]
    rw [hcum0, hL0]
    show ⌈(0 : ℚ) * 2 ^ 2⌉₊ = 0
    have hmul0 : ((0 : ℚ) * 2 ^ 2) = ((0 : ℕ) : ℚ) := by norm_num
    rw [hmul0, Nat.ceil_natCast]
  have hI1 : codeInt fairTwo 1 = 2 := by
    simp only [codeInt]
    rw [hcum1, hL1]
    show ⌈(1 / 2 : ℚ) * 2 ^ 2⌉₊ = 2
    have hmul : ((1 / 2 : ℚ) * 2 ^ 2) = ((2 : ℕ) : ℚ) := by norm_num
    rw [hmul, Nat.ceil_natCast]
  have hC0 : arithCode fairTwo 0 = [false, false] := by
    simp only [arithCode]
    rw [hL0, hI0]
    decide
  have hC1 : arithCode fairTwo 1 = [true, false] := by
    simp only [arithCode]
    rw [hL1, hI1]
    decide
  refine ⟨hC0, hC1, ?_, ?_⟩
  · rw [hC0]; rfl
  · rw [hC1]; rfl

/-- The fair two-symbol code is prefix-free by the general theorem at a
concrete assignment. -/
theorem fairTwo_isPrefixFree : IsPrefixFree (arithCode fairTwo) := by
  apply arithCode_isPrefixFree
  · intro i
    simp only [fairTwo]
    norm_num
  · simp only [fairTwo, Fin.sum_univ_two]
    norm_num

/-- The asymmetric four-symbol distribution `(1/8, 1/2, 1/4, 1/8)`. -/
def asymFour : Fin 4 → ℚ := ![1/8, 1/2, 1/4, 1/8]

/-- The asymmetric four-symbol codewords and their lengths. -/
theorem arithCode_asymFour :
    arithCode asymFour 0 = [false, false, false, false] ∧
    arithCode asymFour 1 = [false, true] ∧
    arithCode asymFour 2 = [true, false, true] ∧
    arithCode asymFour 3 = [true, true, true, false] ∧
    (arithCode asymFour 0).length = 4 ∧
    (arithCode asymFour 1).length = 2 ∧
    (arithCode asymFour 2).length = 3 ∧
    (arithCode asymFour 3).length = 4 := by
  have logb8 : Real.logb 2 (8:ℝ) = 3 := by
    have h8 : (8:ℝ) = 2 ^ 3 := by norm_num
    rw [h8, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have logb2 : Real.logb 2 (2:ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  have logb4 : Real.logb 2 (4:ℝ) = 2 := by
    have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hcum0 : cum asymFour 0 = 0 := by
    simp only [cum, Finset.sum_filter, Fin.sum_univ_four, asymFour]
    norm_num
  have hcum1 : cum asymFour 1 = 1/8 := by
    simp only [cum, Finset.sum_filter, Fin.sum_univ_four, asymFour]
    norm_num
  have hcum2 : cum asymFour 2 = 5/8 := by
    simp only [cum, Finset.sum_filter, Fin.sum_univ_four, asymFour]
    norm_num
  have hcum3 : cum asymFour 3 = 7/8 := by
    simp only [cum, Finset.sum_filter, Fin.sum_univ_four, asymFour]
    norm_num
  have hlen0 : codeLen asymFour 0 = 4 := by
    have hq : ((asymFour 0 : ℚ):ℝ)⁻¹ = 8 := by
      simp only [asymFour]
      norm_num
    simp only [codeLen, hq, logb8]
    norm_num
  have hlen1 : codeLen asymFour 1 = 2 := by
    have hq : ((asymFour 1 : ℚ):ℝ)⁻¹ = 2 := by
      simp only [asymFour]
      norm_num
    simp only [codeLen, hq, logb2]
    norm_num
  have hlen2 : codeLen asymFour 2 = 3 := by
    have hq : ((asymFour 2 : ℚ):ℝ)⁻¹ = 4 := by
      simp only [asymFour]
      norm_num
    simp only [codeLen, hq, logb4]
    norm_num
  have hlen3 : codeLen asymFour 3 = 4 := by
    have hq : ((asymFour 3 : ℚ):ℝ)⁻¹ = 8 := by
      simp only [asymFour]
      norm_num
    simp only [codeLen, hq, logb8]
    norm_num
  have hInt0 : codeInt asymFour 0 = 0 := by
    have hprod : (0:ℚ) * 2 ^ 4 = 0 := by norm_num
    simp only [codeInt, hcum0, hlen0, hprod]
    norm_num
  have hInt1 : codeInt asymFour 1 = 1 := by
    have hprod : (1/8:ℚ) * 2 ^ 2 = 1/2 := by norm_num
    simp only [codeInt, hcum1, hlen1, hprod]
    rw [Nat.ceil_eq_iff one_ne_zero]
    norm_num
  have hInt2 : codeInt asymFour 2 = 5 := by
    have hprod : (5/8:ℚ) * 2 ^ 3 = 5 := by norm_num
    simp only [codeInt, hcum2, hlen2, hprod]
    norm_num
  have hInt3 : codeInt asymFour 3 = 14 := by
    have hprod : (7/8:ℚ) * 2 ^ 4 = 14 := by norm_num
    simp only [codeInt, hcum3, hlen3, hprod]
    norm_num
  have w0 : arithCode asymFour 0 = [false, false, false, false] := by
    simp only [arithCode, hlen0, hInt0]
    decide
  have w1 : arithCode asymFour 1 = [false, true] := by
    simp only [arithCode, hlen1, hInt1]
    decide
  have w2 : arithCode asymFour 2 = [true, false, true] := by
    simp only [arithCode, hlen2, hInt2]
    decide
  have w3 : arithCode asymFour 3 = [true, true, true, false] := by
    simp only [arithCode, hlen3, hInt3]
    decide
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_⟩
  · simp [w0]
  · simp [w1]
  · simp [w2]
  · simp [w3]

/-- The asymmetric four-symbol code is prefix-free by the general theorem. -/
theorem asymFour_isPrefixFree : IsPrefixFree (arithCode asymFour) := by
  apply arithCode_isPrefixFree
  · intro i
    fin_cases i <;> simp only [asymFour] <;> norm_num
  · simp only [asymFour, Fin.sum_univ_four]
    norm_num

end MathlibExt.InformationTheory.ArithmeticCoding.Tests
