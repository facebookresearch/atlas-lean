/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.TriangularIsingSymbol
import Code.FrontierA.QuantumIsingTrotterLocal










namespace StatMech.FrontierA

private theorem sinh_neg_log_eq {x : Real} (hx : 0 < x) :
    Real.sinh (-Real.log x) = (1 - x ^ 2) / (2 * x) := by
  rw [Real.sinh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']

private theorem cosh_neg_log_eq {x : Real} (hx : 0 < x) :
    Real.cosh (-Real.log x) = (1 + x ^ 2) / (2 * x) := by
  rw [Real.cosh_eq, Real.exp_neg, neg_neg, Real.exp_log hx]
  field_simp [hx.ne']

theorem cosh_div_sinh_neg_log {x : Real} (hx : 0 < x) (hx1 : x < 1) :
    Real.cosh (-Real.log x) / Real.sinh (-Real.log x) =
      (1 + x ^ 2) / (1 - x ^ 2) := by
  rw [sinh_neg_log_eq hx, cosh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]

theorem one_div_sinh_neg_log {x : Real} (hx : 0 < x) (hx1 : x < 1) :
    1 / Real.sinh (-Real.log x) = 2 * x / (1 - x ^ 2) := by
  rw [sinh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]

private theorem reduced_symbol_algebra
    (t x k q : Real) (hx : 0 < x) (hx1 : x < 1) :
    (Real.cosh t * Real.cosh (-Real.log x) -
        (Real.sinh t * (-Real.cos k) +
          Real.sinh (-Real.log x) * Real.cos q)) /
        Real.sinh (-Real.log x) =
      Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
        Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k -
        Real.cos q := by
  rw [sinh_neg_log_eq hx, cosh_neg_log_eq hx]
  have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp [hx.ne', hden]
  ring

noncomputable def quantumIsingTrotterReducedParameter
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  let t := beta / (2 * n)
  let x := beta * h / (2 * n)
  Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
    Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k

theorem triangularIsingTrotterSymbol_reduced
    (beta h : Real) (n : Nat) (k q : Real)
    (hx : 0 < beta * h / (2 * n)) (hx1 : beta * h / (2 * n) < 1) :
    triangularIsingSymbol (beta / (4 * n))
        (quantumIsingVerticalCoupling beta h n) 0 (k + Real.pi) q /
        Real.sinh (2 * quantumIsingVerticalCoupling beta h n) =
      quantumIsingTrotterReducedParameter beta h n k - Real.cos q := by
  let x := beta * h / (2 * n)
  have hJ : 2 * quantumIsingVerticalCoupling beta h n = -Real.log x := by
    unfold quantumIsingVerticalCoupling
    dsimp [x]
    ring
  have hsinh : Real.sinh (-Real.log x) ≠ 0 := by
    rw [sinh_neg_log_eq hx]
    have hden : 1 - x ^ 2 ≠ 0 := by nlinarith
    positivity
  unfold triangularIsingSymbol quantumIsingTrotterReducedParameter
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, add_zero,
    Real.cos_add_pi]
  rw [show 2 * (beta / (4 * (n : Real))) = beta / (2 * n) by ring, hJ]
  simpa [x] using reduced_symbol_algebra
    (beta / (2 * (n : Real))) x k q hx hx1

end StatMech.FrontierA
