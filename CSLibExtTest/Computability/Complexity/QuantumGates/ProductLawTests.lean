/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ProductLaw
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tests: product law for disjoint registers
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QMA

#print axioms eventWeight_blockProd
#print axioms thresholdWeight_blockProd

private theorem sum_fin_two_pow (n : ℕ) (h : n = 1) (f : Fin (2 ^ n) → ℝ) :
    ∑ s, f s = f 0 + f 1 := by
  subst h
  show (∑ s : Fin 2, f s) = f 0 + f 1
  exact Fin.sum_univ_two f

private theorem sum_fin_two_mul_one (f : Fin (2 ^ (2 * 1)) → ℝ) :
    ∑ s, f s = f 0 + f 1 + f 2 + f 3 := by
  show (∑ s : Fin 4, f s) = f 0 + f 1 + f 2 + f 3
  exact Fin.sum_univ_four f

private theorem ap_true : acceptProb (basisState [true]) = 1 := by
  unfold acceptProb
  rw [sum_fin_two_pow _ (show [true].length = 1 from rfl)]
  have h0 : ¬ qBit 0 (0 : Fin (2 ^ [true].length)).val = 1 := by decide
  have h1 : qBit 0 (1 : Fin (2 ^ [true].length)).val = 1 := by decide
  rw [ite_eq_right h0, ite_eq_left h1]
  have hb : basisState [true] (1 : Fin (2 ^ [true].length)) = 1 := rfl
  rw [hb]
  simp

private theorem ap_false : acceptProb (basisState [false]) = 0 := by
  unfold acceptProb
  rw [sum_fin_two_pow _ (show [false].length = 1 from rfl)]
  have h0 : ¬ qBit 0 (0 : Fin (2 ^ [false].length)).val = 1 := by decide
  have h1 : qBit 0 (1 : Fin (2 ^ [false].length)).val = 1 := by decide
  rw [ite_eq_right h0, ite_eq_left h1]
  have hb : basisState [false] (1 : Fin (2 ^ [false].length)) = 0 := rfl
  rw [hb]
  simp

private theorem ac_tt : acceptCount ![true, true] = 2 := by
  unfold acceptCount
  rw [Fin.sum_univ_two]
  norm_num

private theorem ac_tf : acceptCount ![true, false] = 1 := by
  unfold acceptCount
  rw [Fin.sum_univ_two]
  norm_num

private theorem ac_ft : acceptCount ![false, true] = 1 := by
  unfold acceptCount
  rw [Fin.sum_univ_two]
  norm_num

private theorem ac_ff : acceptCount ![false, false] = 0 := by
  unfold acceptCount
  rw [Fin.sum_univ_two]
  norm_num

private theorem f_tt : (∏ i : Fin 2, if ![true, true] i then (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i else 1 - (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i) = 0 := by
  rw [Fin.prod_univ_two]
  norm_num [ap_true, ap_false]

private theorem f_tf : (∏ i : Fin 2, if ![true, false] i then (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i else 1 - (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i) = 1 := by
  rw [Fin.prod_univ_two]
  norm_num [ap_true, ap_false]

private theorem f_ft : (∏ i : Fin 2, if ![false, true] i then (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i else 1 - (fun i : Fin 2 => acceptProb (if i = 0 then basisState [true] else basisState [false])) i) = 0 := by
  rw [Fin.prod_univ_two]
  norm_num [ap_true, ap_false]

/-- Two one-qubit blocks in basis states `|1⟩` and `|0⟩`: the output-bit
event "both accept" has weight `0`, the event "first accepts" has
weight `1`, and the threshold-`1` weight is `1`. -/
theorem productLaw_two_block_example :
    (∑ s : Fin (2 ^ (2 * 1)),
        if (fun i => decide (qBit 0 (blockDigit 2 1 i s).val = 1)) =
            (fun _ => true) then
          (starRingEnd ℂ
              (blockProd (fun i : Fin 2 => if i = 0 then basisState [true]
                else basisState [false]) s) *
            blockProd (fun i : Fin 2 => if i = 0 then basisState [true]
              else basisState [false]) s).re else 0) = 0 ∧
      tailWeight (fun i : Fin 2 => acceptProb
          (if i = 0 then basisState [true] else basisState [false])) 1 = 1 := by
  constructor
  · rw [sum_fin_two_mul_one]
    have c0 : ¬ (fun i : Fin 2 => decide (qBit 0 (blockDigit 2 1 i (0 : Fin (2 ^ (2 * 1)))).val = 1)) = (fun _ => true) := by decide
    have c1 : ¬ (fun i : Fin 2 => decide (qBit 0 (blockDigit 2 1 i (1 : Fin (2 ^ (2 * 1)))).val = 1)) = (fun _ => true) := by decide
    have c2 : ¬ (fun i : Fin 2 => decide (qBit 0 (blockDigit 2 1 i (2 : Fin (2 ^ (2 * 1)))).val = 1)) = (fun _ => true) := by decide
    have c3 : (fun i : Fin 2 => decide (qBit 0 (blockDigit 2 1 i (3 : Fin (2 ^ (2 * 1)))).val = 1)) = (fun _ => true) := by decide
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3]
    have hbp : blockProd (fun i : Fin 2 => if i = 0 then basisState [true] else basisState [false]) (3 : Fin (2 ^ (2 * 1))) = 0 := by
      unfold blockProd
      rw [Fin.prod_univ_two]
      simp [show (1 : Fin 2) ≠ 0 from by decide]
      exact Or.inr rfl
    rw [hbp]
    simp
  · unfold tailWeight
    rw [Finset.sum_filter]
    rw [← Equiv.sum_comp (finTwoArrowEquiv Bool).symm]
    simp only [finTwoArrowEquiv_symm_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [ac_tt, ac_tf, ac_ft, ac_ff,
      ite_eq_left (show (1 : ℝ) ≤ 2 from by norm_num),
      ite_eq_left (show (1 : ℝ) ≤ 1 from by norm_num),
      ite_eq_right (show ¬ (1 : ℝ) ≤ 0 from by norm_num)]
    rw [f_tt, f_tf, f_ft]
    norm_num

end Cslib.Complexity.Classes.Tests
