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
# Production-decay (exposure-age) model

With constant production `P` and decay `λ > 0`,
`N(t) = N0*exp(-λ*t) + (P/λ)*(1-exp(-λ*t))` solves `N' = P - λ*N`
and starts at `N0`.

## i. Overview

Constant production, no erosion or shielding changes, on `t ≥ 0`.
Saturation bounds and age inversion are separate results. Multi-clock
and repeated-rate Bateman limits remain later tasks.

## ii. Key results

- `EarthScience.production_decay_hasDerivAt`: the production-decay
  function satisfies `N' = P - λ*N`.
- `EarthScience.production_decay_initial`: `N(0) = N0`.

## iii. References

- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Production-decay (exposure-age) model: with constant production `P ≥ 0`
and decay `λ > 0`,
`N(t) = N0*exp(-λ*t) + (P/λ)*(1-exp(-λ*t))` solves `N' = P - λ*N`. -/
theorem production_decay_hasDerivAt (P lam N0 t : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t => N0 * Real.exp (-lam * t) +
        (P / lam) * (1 - Real.exp (-lam * t)))
      (P - lam * (N0 * Real.exp (-lam * t) +
        (P / lam) * (1 - Real.exp (-lam * t)))) t := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hlin : HasDerivAt (fun t : ℝ => -lam * t) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-lam * t))
      (Real.exp (-lam * t) * -lam) t :=
    hlin.exp
  have h1 : HasDerivAt (fun t : ℝ => N0 * Real.exp (-lam * t))
      (N0 * (Real.exp (-lam * t) * -lam)) t :=
    hexp.const_mul N0
  have hsub : HasDerivAt (fun t : ℝ => 1 - Real.exp (-lam * t))
      (-(Real.exp (-lam * t) * -lam)) t :=
    hexp.const_sub 1
  have h2 : HasDerivAt (fun t : ℝ => (P / lam) * (1 - Real.exp (-lam * t)))
      ((P / lam) * (-(Real.exp (-lam * t) * -lam))) t :=
    hsub.const_mul (P / lam)
  have h := h1.add h2
  convert h using 1
  field_simp
  ring

/-- Production-decay starts at `N0`. -/
theorem production_decay_initial (P lam N0 : ℝ) :
    N0 * Real.exp (-lam * 0) + (P / lam) * (1 - Real.exp (-lam * 0)) = N0 := by
  simp

end EarthScience
