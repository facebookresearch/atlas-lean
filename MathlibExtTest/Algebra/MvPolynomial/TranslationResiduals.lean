/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.MvPolynomial.TranslationResiduals

/-!
# Tests of translated real polynomial fits

Residuals are compared on the corresponding rows, not at the same numerical coordinate.
Empty data and zero-dimensional real inputs are permitted.
-/

open MvPolynomial

-- Two distinct rows with arbitrary real responses and an arbitrary polynomial.
example (p : MvPolynomial Unit ℝ) (a b c : ℝ) :
    let q := aeval (fun i => X i + C a) p
    (b - eval (fun _ => -a) q) ^ 2 + (c - eval (fun _ => 1 - a) q) ^ 2 =
      (b - eval (fun _ => 0) p) ^ 2 + (c - eval (fun _ => 1) p) ^ 2 := by
  let rows (i : Bool) (_ : Unit) : ℝ := if i then 1 else 0
  let resp (i : Bool) := if i then c else b
  have h := (polynomialTranslation_residuals_and_topCoefficients
    p (fun _ => a) rows resp Finset.univ).2.2.1
  simpa only [Fintype.sum_bool, rows, resp, ite_true, Bool.false_eq_true, ite_false, Pi.sub_def,
    zero_sub, add_comm] using h

-- Degree zero has one exponent vector even with no variables. No observed rows are needed.
example (c : ℝ) (a : Empty → ℝ) :
    (aeval (fun i => X i + C (a i)) (C c : MvPolynomial Empty ℝ)).coeff 0 = c := by
  have h := (polynomialTranslation_residuals_and_topCoefficients (C c) a
    (fun j : Empty => nomatch j) (fun j : Empty => nomatch j) ∅).2.2.2 0 (by simp)
  simpa only [coeff_zero_C] using h
