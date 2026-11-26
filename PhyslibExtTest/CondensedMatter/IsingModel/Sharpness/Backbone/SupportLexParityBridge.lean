/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexParityBridge

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexParityBridge`

* `shb_paritySeriesMass_eq_cosh_mul_polynomial` and
  `shb_paritySeriesMassOn_eq_cosh_mul_polynomial` on `Fin 2`;
* `shb_supportLex_realParity_P3_counterexample` and `shb_supportLex_series_P3_counterexample`
  (unconditional counterexamples), and their agreement via `shbK4DirectRhoSeries_eq_polynomial`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexParityBridge

open _root_.StatMech.Sharpness

-- Parity series as `cosh^|E|` times a parity polynomial.
example (x : ℝ) : shbParitySeriesMass (E := Fin 2) (fun _ => True) x =
    Real.cosh x ^ 2 * shbParityPolynomial (E := Fin 2) (fun _ => True) (Real.tanh x) := by
  simpa using shb_paritySeriesMass_eq_cosh_mul_polynomial (E := Fin 2) (fun _ => True) x

-- The same on a finite subset.
example (S : Finset (Fin 3)) (x : ℝ) :=
  shb_paritySeriesMassOn_eq_cosh_mul_polynomial S (fun _ => True) x

-- The parity polynomial counterexample at `2/3`.
example : shbK4DirectRhoPolynomial shbK4H (2 / 3) < shbK4DirectRhoPolynomial shbK4G (2 / 3) :=
  shb_supportLex_realParity_P3_counterexample

-- The series counterexample, rewritten through the polynomial identity.
example : shbK4DirectRhoPolynomial shbK4H (Real.tanh (Real.artanh (2 / 3))) <
    shbK4DirectRhoPolynomial shbK4G (Real.tanh (Real.artanh (2 / 3))) := by
  rw [← shbK4DirectRhoSeries_eq_polynomial, ← shbK4DirectRhoSeries_eq_polynomial]
  exact shb_supportLex_series_P3_counterexample

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexParityBridge
