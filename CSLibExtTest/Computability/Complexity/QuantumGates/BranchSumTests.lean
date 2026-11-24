/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.BranchSum

/-!
# Tests: kept-index branch sum
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes

#print axioms acceptProb_branchState
#print axioms acceptProb_branchState_grouped

private theorem qBit_zero_zero : qBit 0 0 = 0 := by decide

private theorem qBit_zero_one : qBit 0 1 = 1 := by decide

private theorem qNumOf_false : qNumOf [false] = 0 := by decide

private theorem qNumOf_true : qNumOf [true] = 1 := by decide

private theorem acceptProb_basisState_false : acceptProb (basisState [false]) = 0 := by
  have h2 : ∀ (f : Fin (2 ^ [false].length) → ℝ), ∑ s, f s = f 0 + f 1 :=
    fun f => Fin.sum_univ_two f
  unfold acceptProb basisState
  rw [h2]
  simp [qBit_zero_zero, qBit_zero_one, qNumOf_false]

private theorem acceptProb_basisState_true : acceptProb (basisState [true]) = 1 := by
  have h2 : ∀ (f : Fin (2 ^ [true].length) → ℝ), ∑ s, f s = f 0 + f 1 :=
    fun f => Fin.sum_univ_two f
  unfold acceptProb basisState
  rw [h2]
  simp [qBit_zero_zero, qBit_zero_one, qNumOf_true]

private theorem normSq_three_fifths : Complex.normSq (3 / 5 : ℂ) = 9 / 25 := by
  norm_num [Complex.normSq_div, Complex.normSq_ofNat]

private theorem normSq_four_fifths_I :
    Complex.normSq ((4 / 5 : ℂ) * Complex.I) = 16 / 25 := by
  norm_num [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_div, Complex.normSq_ofNat]

/-- Two branches on one work qubit: branch `0` is the basis state `|0⟩`
(acceptance `0`), branch `1` is `|1⟩` (acceptance `1`), with amplitudes
`3/5` and `4/5` (times a phase on the second branch). The acceptance
probability of the branch state is `16/25`, and its squared norm is `1`. -/
theorem branchState_two_branch_example :
    acceptProb (branchState (m := 1) (t := 1)
        (fun r => if r = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I)
        (fun r => if r = 0 then basisState [false] else basisState [true])) =
        16 / 25 ∧
      sqNorm (branchState (m := 1) (t := 1)
        (fun r => if r = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I)
        (fun r => if r = 0 then basisState [false] else basisState [true])) =
        1 := by
  have hsum : ∀ (f : Fin (2 ^ 1) → ℝ), ∑ r, f r = f 0 + f 1 :=
    fun f => Fin.sum_univ_two f
  have c1 : (1 : Fin (2 ^ 1)) ≠ 0 := by decide
  rw [acceptProb_branchState (hm := le_rfl), sqNorm_branchState, hsum, hsum]
  constructor
  · simp only [ite_true, ite_false, c1]
    rw [acceptProb_basisState_false, acceptProb_basisState_true, normSq_three_fifths,
      normSq_four_fifths_I]
    norm_num
  · simp only [ite_true, ite_false, c1]
    rw [sqNorm_basisState, sqNorm_basisState, normSq_three_fifths, normSq_four_fifths_I]
    norm_num

end Cslib.Complexity.Classes.Tests
