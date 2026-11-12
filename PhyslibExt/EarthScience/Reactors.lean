/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Well-mixed reactors (CSTR) and plug-flow residence time

For `V*c' = Q*(cin-c) - k*V*c`, the CSTR solution
`c(t) = cstar + (c0-cstar)*exp(-(Q/V+k)*t)` with
`cstar = Q*cin/(Q+k*V)` satisfies the ODE, `cstar` is the steady state,
and a plug-flow parcel `c(s) = cin*exp(-k*s)` satisfies `c' = -k*c`,
so at residence time `τ = V/Q`, `c_out = cin*exp(-k*τ)`.

## i. Overview

`V, Q > 0`, `k ≥ 0`, `cin, c0 ≥ 0`, `t ≥ 0`. The fixed-volume CSTR and
the ideal no-mixing-along-flow PFR are explicitly different models; this
file proves each one's solution formula separately. `Q = 0` is a separate
closed-reactor formula, not division by zero, and is not covered here.

## ii. Key results

- `EarthScience.cstr_hasDerivAt`: the CSTR solution satisfies the ODE.
- `EarthScience.cstr_steady_state`: `cstar` makes the ODE right-hand
  side vanish.
- `EarthScience.plugFlow_hasDerivAt`: a plug-flow parcel satisfies `c' = -k*c`.

## iii. References

- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
-/

@[expose] public section

namespace EarthScience

/-- CSTR: for `V*c' = Q*(cin-c) - k*V*c`, i.e. `c' = (Q/V)*(cin-c) - k*c`,
the solution `c(t) = cstar + (c0-cstar)*exp(-(Q/V+k)*t)` with
`cstar = Q*cin/(Q+k*V)` satisfies the ODE at every `t`. -/
theorem cstr_hasDerivAt (V Q k cin c0 t : ℝ) (hV : 0 < V) (hQ : 0 < Q) (hk : 0 ≤ k) :
    HasDerivAt (fun t => Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t))
      ((Q / V) * (cin - (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t))) -
        k * (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t))) t := by
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hQkV : Q + k * V ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hQ (le_add_of_nonneg_right (mul_nonneg hk hV.le)))
  have hlin : HasDerivAt (fun t => (-(Q / V + k)) * t) (-(Q / V + k)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(Q / V + k))
  have hexp : HasDerivAt (fun t => Real.exp ((-(Q / V + k)) * t))
      (Real.exp ((-(Q / V + k)) * t) * (-(Q / V + k))) t := hlin.exp
  have hmul : HasDerivAt
      (fun t => (c0 - Q * cin / (Q + k * V)) * Real.exp ((-(Q / V + k)) * t))
      ((c0 - Q * cin / (Q + k * V)) * (Real.exp ((-(Q / V + k)) * t) * (-(Q / V + k)))) t :=
    hexp.const_mul (c0 - Q * cin / (Q + k * V))
  have hadd : HasDerivAt
      (fun t => Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp ((-(Q / V + k)) * t))
      ((c0 - Q * cin / (Q + k * V)) * (Real.exp ((-(Q / V + k)) * t) * (-(Q / V + k)))) t :=
    hmul.const_add (Q * cin / (Q + k * V))
  have heq : (c0 - Q * cin / (Q + k * V)) * (Real.exp ((-(Q / V + k)) * t) * (-(Q / V + k))) =
      (Q / V) * (cin - (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t))) -
        k * (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t)) := by
    field_simp
    ring
  rw [heq] at hadd
  exact hadd

/-- CSTR steady state: `cstar = Q*cin/(Q+k*V)` makes the right-hand side
`(Q/V)*(cin-cstar) - k*cstar` vanish. -/
theorem cstr_steady_state (V Q k cin : ℝ) (hV : 0 < V) (hQ : 0 < Q) (hk : 0 ≤ k) :
    (Q / V) * (cin - Q * cin / (Q + k * V)) - k * (Q * cin / (Q + k * V)) = 0 := by
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hQkV : Q + k * V ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hQ (le_add_of_nonneg_right (mul_nonneg hk hV.le)))
  field_simp
  ring

/-- Plug-flow parcel: along a parcel, `c(s) = cin*exp(-k*s)` satisfies
`c' = -k*c`; at residence time `τ = V/Q` this gives
`c_out = cin*exp(-k*τ)`. -/
theorem plugFlow_hasDerivAt (k cin s : ℝ) :
    HasDerivAt (fun s => cin * Real.exp (-k * s))
      (-k * (cin * Real.exp (-k * s))) s := by
  have hlin : HasDerivAt (fun s => -k * s) (-k) s := by
    simpa using (hasDerivAt_id s).const_mul (-k)
  have hexp : HasDerivAt (fun s => Real.exp (-k * s)) (Real.exp (-k * s) * -k) s :=
    hlin.exp
  have hmul : HasDerivAt (fun s => cin * Real.exp (-k * s))
      (cin * (Real.exp (-k * s) * -k)) s :=
    hexp.const_mul cin
  have heq : cin * (Real.exp (-k * s) * -k) = -k * (cin * Real.exp (-k * s)) := by
    ring
  rw [heq] at hmul
  exact hmul

end EarthScience
