/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Fixed PK log-observation identity

For known dose `D > 0` and volume `V > 0`, the concentration observation
`Y j = (D / V) * exp (-k * t j) * exp (ε j)` has log exactly
the linear form `log (D / V) + (-t j) * k + ε j`: the design row is
`(1, -t j)` and the coefficient vector is `(log (D / V), k)`. This is
an exact identity for every value of the errors; additive concentration
noise would not be additive log noise, and the log output is well
defined because `Y j > 0`.

Model mathematics only; no estimation or dosing claim.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.PharmacokineticObservation

/-- **PK log-observation identity (multiplicative form).** For known `D > 0`, `V > 0`, the
concentration observation `Y j = (D / V) * exp (-k * t j) * exp (ε j)` (the bolus concentration
times a log-additive error factor) has log exactly the linear form
`1 * log (D / V) + (-t j) * k + ε j`: the design row is `(1, -t j)` and the coefficient vector is
`(log (D / V), k)`. This is an exact identity for every value of the errors; additive concentration
noise would not be additive log noise. -/
lemma pk_log_law {D V k : ℝ} (hD : 0 < D) (hV : 0 < V) {n : ℕ}
    (t ε : Fin n → ℝ) (j : Fin n) :
    Real.log ((D / V) * Real.exp (-k * t j) * Real.exp (ε j)) =
      1 * Real.log (D / V) + (-t j) * k + ε j := by
  have hDV : D / V ≠ 0 := ne_of_gt (div_pos hD hV)
  have h1 : Real.exp (-k * t j) ≠ 0 := (Real.exp_pos _).ne'
  have h2 : Real.exp (ε j) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.log_mul (mul_ne_zero hDV h1) h2, Real.log_mul hDV h1,
    Real.log_exp, Real.log_exp]
  ring

end MathlibExt.Biology.Biophysics.PharmacokineticObservation
