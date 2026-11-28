/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.LucasPolytopicNumberClosedForm
import MathlibExt.NumberTheory.LucasPolytopicNumberDerivative

namespace MetaMathlibExt

open scoped BigOperators Topology

private theorem hasDerivAt_one_sub_mul (a : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - a * y) (-a) 0 := by
  simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub
    ((hasDerivAt_id (0 : ℝ)).const_mul a)

-- Compute the first derivative for these roots from the defining cases, not from the iterate.
private theorem firstDerivative (x : ℝ) (hx : (1 - 3 * x) * (1 - 2 * x) ≠ 0) :
    lucasDerivative 3 2 (fun y => 1 / (1 - y)) x = 1 / ((1 - 3 * x) * (1 - 2 * x)) := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · rw [lucasDerivative_zero]
    have h : HasDerivAt (fun y : ℝ => 1 - y) (-1) 0 := by
      simpa using hasDerivAt_one_sub_mul 1
    simpa using ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_div h (by norm_num)).deriv
  · rcases mul_ne_zero_iff.mp hx with ⟨h₃, h₂⟩
    rw [lucasDerivative_of_ne_zero _ _ _ hx₀]
    rw [show (3 : ℝ) - 2 = 1 by norm_num, one_mul]
    rw [div_sub_div _ _ h₃ h₂, div_div]
    simp only [one_mul, mul_one]
    rw [show (1 - 2 * x) - (1 - 3 * x) = x by ring]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) ((1 - 3 * x) * (1 - 2 * x)) hx₀

-- The zero-fold iterate is the geometric kernel itself.
example : (lucasDerivative 3 2)^[0] (fun y => 1 / (1 - y)) (-1) = 1 / 2 := by
  norm_num

-- At a nonzero point the second iterate is a divided difference of two explicit values.
example : (lucasDerivative 3 2)^[2] (fun y => 1 / (1 - y)) (-1) = 1 / 70 := by
  rw [Function.iterate_succ_apply', lucasDerivative_of_ne_zero _ _ _ (by norm_num),
    Function.iterate_one]
  rw [firstDerivative _ (by norm_num), firstDerivative _ (by norm_num)]
  norm_num

-- At zero the second iterate is the ordinary derivative of the first iterate near zero.
example : (lucasDerivative 3 2)^[2] (fun y => 1 / (1 - y)) 0 = 5 := by
  rw [Function.iterate_succ_apply', Function.iterate_one, lucasDerivative_zero]
  have hd : HasDerivAt (fun y : ℝ => (1 - 3 * y) * (1 - 2 * y)) (-5) 0 := by
    convert (hasDerivAt_one_sub_mul 3).fun_mul (hasDerivAt_one_sub_mul 2) using 1
    norm_num
  have hnz : (1 - 3 * (0 : ℝ)) * (1 - 2 * 0) ≠ 0 := by norm_num
  have heq : lucasDerivative 3 2 (fun y => 1 / (1 - y)) =ᶠ[𝓝 0]
      (fun y => 1 / ((1 - 3 * y) * (1 - 2 * y))) :=
    (hd.continuousAt.eventually_ne hnz).mono fun y hy => firstDerivative y hy
  simpa using
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_div hd hnz).congr_of_eventuallyEq heq).deriv

-- At x = 1/9 the denominator vanishes for n = 2 and roots 3 and 2.
example : ∏ k ∈ Finset.range (2 + 1), (1 - (3 : ℝ) ^ (2 - k) * 2 ^ k * (1 / 9)) = 0 := by
  norm_num [Finset.prod_range_succ]

-- The same nonzero-point value is available through the public theorem.
example (P : LucasParameters) (hs : 3 + 2 = P.s) (ht : 3 * 2 = -P.t) :
    (lucasDerivative 3 2)^[2] (fun y => 1 / (1 - y)) (-1) = 1 / 70 := by
  have h₁ := lucasBracket_closed_form P 3 2 hs ht 1
  have h₂ := lucasBracket_closed_form P 3 2 hs ht 2
  norm_num at h₁ h₂
  rw [iterate_lucasDerivative_inv_one_sub P 3 2 hs ht (by norm_num) 2 (-1)
    (by norm_num [Finset.prod_range_succ])]
  norm_num [lucasFactorial_succ, h₁, h₂, Finset.prod_range_succ]

#print axioms iterate_lucasDerivative_inv_one_sub

end MetaMathlibExt
