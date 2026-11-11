/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.E01Reactors

/-!
# Reactor checks

Concrete consumers of `PhyslibExt.EarthScience.E01Reactors`: the
witness `V = Q = k = cin = 1`, `c0 = 0` giving `cstar = 1/2`, the
`k = 0` conservative-throughflow case, and a plug-flow parcel.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`V = Q = k = cin = 1` and `c0 = 0`, the steady state is `1/2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.E01Reactors`
-/

/-- Witness: with `V = Q = k = cin = 1`, `cstar = 1/2`. -/
example : (1 : ℝ) * 1 / (1 + 1 * 1) = 1 / 2 := by norm_num

/-- Witness: the steady state is a zero of the CSTR right-hand side. -/
example : (1 / 1 : ℝ) * (1 - 1 * 1 / (1 + 1 * 1)) - 1 * (1 * 1 / (1 + 1 * 1)) = 0 :=
  EarthScience.cstr_steady_state 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- Witness: the CSTR solution satisfies the ODE at `t = 1`. -/
example : HasDerivAt (fun t : ℝ => 1 * 1 / (1 + 1 * 1) +
    (0 - 1 * 1 / (1 + 1 * 1)) * Real.exp (-(1 / 1 + 1) * t))
    ((1 / 1) * (1 - (1 * 1 / (1 + 1 * 1) +
      (0 - 1 * 1 / (1 + 1 * 1)) * Real.exp (-(1 / 1 + 1) * 1))) -
      1 * (1 * 1 / (1 + 1 * 1) +
      (0 - 1 * 1 / (1 + 1 * 1)) * Real.exp (-(1 / 1 + 1) * 1))) 1 :=
  EarthScience.cstr_hasDerivAt 1 1 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)

/-- Degenerate case `k = 0`: conservative throughflow, `cstar = cin`. -/
example (V Q cin : ℝ) (hV : 0 < V) (hQ : 0 < Q) :
    (Q / V) * (cin - Q * cin / (Q + 0 * V)) - 0 * (Q * cin / (Q + 0 * V)) = 0 :=
  EarthScience.cstr_steady_state V Q 0 cin hV hQ le_rfl

/-- Plug-flow parcel: `cin = 1`, `k = 1` gives outlet `exp(-1)` at `τ = 1`. -/
example (s : ℝ) : HasDerivAt (fun s : ℝ => 1 * Real.exp (-1 * s))
    (-1 * (1 * Real.exp (-1 * s))) s :=
  EarthScience.plugFlow_hasDerivAt 1 1 s
