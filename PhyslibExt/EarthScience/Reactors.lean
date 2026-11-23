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
import PhyslibExt.EarthScience.FirstOrderKinetics
/-!
# Well-mixed reactor (CSTR)

For `V*c' = Q*(cin-c) - k*V*c`, the CSTR solution
`c(t) = cstar + (c0-cstar)*exp(-(Q/V+k)*t)` with
`cstar = Q*cin/(Q+k*V)` satisfies the ODE, and `cstar` is the steady state.

## i. Overview

`V, Q > 0`, `k ≥ 0`, `cin, c0 ≥ 0`, `t ≥ 0`. The transient
`(c0-cstar)*exp(-(Q/V+k)*t)` is first-order decay at the combined rate
`Q/V + k`, so `cstr_hasDerivAt` follows from
`EarthScience.firstOrder_decay_hasDerivAt`. `Q = 0` is a separate
closed-reactor formula, not division by zero, and is not covered here.

The ideal plug-flow reactor (no mixing along the flow) is a different model and
is not formalized here: a parcel's concentration `cin*exp(-k*s)` obeys
first-order decay, which is `EarthScience.firstOrder_decay_hasDerivAt`, but no
result here relates the parcel at the residence time `V/Q` to the reactor
outlet.

## ii. Key results

- `EarthScience.cstr_hasDerivAt`: the CSTR solution satisfies the ODE.
- `EarthScience.cstr_steady_state`: `cstar` makes the ODE right-hand
  side vanish.

## iii. References

- `EarthScience.firstOrder_decay_hasDerivAt` in
  `PhyslibExt.EarthScience.FirstOrderKinetics` for the decaying transient.
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
  have h := (firstOrder_decay_hasDerivAt (Q / V + k) (c0 - Q * cin / (Q + k * V)) t).const_add
    (Q * cin / (Q + k * V))
  convert h using 1
  field_simp
  ring

/-- CSTR steady state: `cstar = Q*cin/(Q+k*V)` makes the right-hand side
`(Q/V)*(cin-cstar) - k*cstar` vanish. -/
theorem cstr_steady_state (V Q k cin : ℝ) (hV : 0 < V) (hQ : 0 < Q) (hk : 0 ≤ k) :
    (Q / V) * (cin - Q * cin / (Q + k * V)) - k * (Q * cin / (Q + k * V)) = 0 := by
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hQkV : Q + k * V ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hQ (le_add_of_nonneg_right (mul_nonneg hk hV.le)))
  field_simp
  ring

end EarthScience
