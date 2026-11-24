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

end MathlibExt.InformationTheory.ArithmeticCoding.Tests
