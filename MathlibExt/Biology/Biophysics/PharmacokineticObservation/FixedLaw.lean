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
# Fixed PK log-observation law

For known dose `D > 0` and volume `V > 0`, the log-concentration
observation `Y j = exp (log (D / V) - k * t j + ε j)` has log exactly
the linear form `log (D / V) + (-t j) * k + ε j`: the design row is
`(1, -t j)` and the coefficient vector is `(log (D / V), k)`. This is
the exact log law of the declared observation; additive concentration
noise would not be additive log noise, and the log output is well
defined because `Y j > 0`.

Model mathematics only; no estimation or dosing claim.
-/

@[expose] public section

open Real

namespace MathlibExt.Biology.Biophysics.PharmacokineticObservation

set_option linter.unusedVariables false in
/-- **PK log-observation law.** For known `D > 0`, `V > 0`, the
log-concentration observation
`Y j = exp (log (D / V) - k * t j + ε j)` has log exactly the linear
form `1 * log (D / V) + (-t j) * k + ε j`: the design row is
`(1, -t j)` and the coefficient vector is `(log (D / V), k)`. This is
the exact log law; additive concentration noise would not be additive
log noise. -/
theorem pk_log_law {D V k : ℝ} (hD : 0 < D) (hV : 0 < V) {n : ℕ}
    (t ε : Fin n → ℝ) (j : Fin n) :
    Real.log (Real.exp (Real.log (D / V) - k * t j + ε j)) =
      1 * Real.log (D / V) + (-t j) * k + ε j := by
  rw [Real.log_exp]
  ring

end MathlibExt.Biology.Biophysics.PharmacokineticObservation
