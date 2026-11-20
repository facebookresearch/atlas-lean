/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingSymbolReduction








namespace StatMech.FrontierA

private theorem reduced_parameter_gap_square (t x : Real) :
    Real.cosh t * (1 + x ^ 2) - 2 * x * Real.sinh t - (1 - x ^ 2) =
      2 * (Real.sinh (t / 2) - x * Real.cosh (t / 2)) ^ 2 := by
  have hcosh := Real.cosh_two_mul (t / 2)
  have hsinh := Real.sinh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hcosh hsinh
  rw [hcosh, hsinh]
  linear_combination (1 - x ^ 2) * hcs

theorem one_le_quantumIsingTrotterReducedParameter
    (beta h : Real) (n : Nat) (k : Real)
    (ht : 0 < beta / (2 * n))
    (hx : 0 < beta * h / (2 * n))
    (hx1 : beta * h / (2 * n) < 1) :
    1 ≤ quantumIsingTrotterReducedParameter beta h n k := by
  let t := beta / (2 * n)
  let x := beta * h / (2 * n)
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hsinh : 0 < Real.sinh t :=
    Real.sinh_pos_iff.mpr (by simpa [t] using ht)
  have hcos := Real.neg_one_le_cos k
  have hgap := reduced_parameter_gap_square t x
  have hsq :
      0 ≤ 2 * (Real.sinh (t / 2) - x * Real.cosh (t / 2)) ^ 2 := by
    positivity
  unfold quantumIsingTrotterReducedParameter
  change 1 ≤ Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
    Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k
  rw [show Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
      Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k =
      (Real.cosh t * (1 + x ^ 2) + 2 * x * Real.sinh t * Real.cos k) /
        (1 - x ^ 2) by field_simp [hden.ne']]
  rw [le_div_iff₀ hden]
  have hcoeff : 0 ≤ 2 * x * Real.sinh t := by positivity
  have hcosBound := mul_le_mul_of_nonneg_left hcos hcoeff
  nlinarith

end StatMech.FrontierA
