/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierC.LeeYangSymmetry

open scoped BigOperators
open Finset Polynomial

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in


theorem zeroFieldInteractionWeight_mul_pow_pos (beta : ℝ) {z : ℝ} (hz : 0 < z)
    (s : ConfigSpace V) :
    0 < zeroFieldInteractionWeight G beta s * z ^ minusSpinCount s := by
  exact mul_pos (Real.exp_pos _) (pow_pos hz _)



theorem eval_leeYangPolynomial_pos (beta : ℝ) {z : ℝ} (hz : 0 < z) :
    0 < (leeYangPolynomial G beta).eval z := by
  rw [eval_leeYangPolynomial]
  exact Finset.sum_pos (fun s _ =>
    zeroFieldInteractionWeight_mul_pow_pos G beta hz s) Finset.univ_nonempty


theorem eval_leeYangComplexPolynomial_ofReal_ne_zero (beta : ℝ) {z : ℝ}
    (hz : 0 < z) :
    (leeYangComplexPolynomial G beta).eval (z : ℂ) ≠ 0 := by
  rw [eval_leeYangComplexPolynomial_ofReal]
  intro hzero
  have : (leeYangPolynomial G beta).eval z = 0 := Complex.ofReal_eq_zero.mp hzero
  exact (eval_leeYangPolynomial_pos G beta hz).ne' this



theorem leeYangComplexPolynomial_not_isRoot_ofReal_pos (beta : ℝ) {z : ℝ}
    (hz : 0 < z) :
    ¬(leeYangComplexPolynomial G beta).IsRoot (z : ℂ) := by
  rw [Polynomial.IsRoot.def]
  exact eval_leeYangComplexPolynomial_ofReal_ne_zero G beta hz

end StatMech.FrontierA
