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

With constant production `P` and decay constant `λ`, the nuclide inventory
`N(t) = N0*exp(-λ*t) + (P/λ)*(1-exp(-λ*t))` solves `N' = P - λ*N`
and starts at `N0`.

## i. Overview

Physical domain: constant production `P ≥ 0`, decay constant `λ > 0`, initial
(inherited) inventory `N0 ≥ 0` and exposure time `t ≥ 0`, with no erosion or
shielding changes. The two theorems are unrestricted algebraic extensions of
this model, separate from the physical statement: `production_decay_hasDerivAt`
holds for every real `P`, `N0` and `t` once `λ > 0`, and
`production_decay_initial` for every real `P`, `λ` and `N0`; only on the
physical domain do they describe a nuclide inventory. For `λ = 0` the displayed
formula is not the physical solution: Lean's division gives `P/0 = 0`, so the
formula is the constant `N0`, whereas the zero-decay solution is `N0 + P*t`;
`production_decay_initial` holds there only because both decay factors equal
`1` at `t = 0`. Saturation bounds and age inversion are separate results.
Multi-clock and repeated-rate Bateman limits remain later tasks.

## ii. Key results

- `EarthScience.production_decay_hasDerivAt`: the production-decay
  function satisfies `N' = P - λ*N`.
- `EarthScience.production_decay_initial`: `N(0) = N0`.

## iii. References

- D. Lal, Cosmic ray labeling of erosion surfaces: in situ nuclide production
  rates and erosion models, Earth Planet. Sci. Lett. 104 (1991) 424–439: the
  in situ build-up of a radionuclide under constant production and decay, the
  basis of exposure dating.
- P. Vermeesch, CosmoCalc: An Excel add-in for cosmogenic nuclide calculations,
  Geochem. Geophys. Geosyst. 8 (2007) Q08003, Section 5.1, Eq. (11): the
  single-nuclide exposure age under zero erosion and burial, the inverse of
  `N = (P/λ)*(1-exp(-λ*t))`, i.e. this model with `N0 = 0` (`P` here is the
  scaled production rate `P S` there).
- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Production-decay (exposure-age) model: for decay constant `λ > 0` and
every real `P`, `N0` and `t`,
`N(t) = N0*exp(-λ*t) + (P/λ)*(1-exp(-λ*t))` solves `N' = P - λ*N`. This is an
unrestricted algebraic identity; it describes a nuclide inventory under constant
production on the physical domain `P ≥ 0`, `N0 ≥ 0`, `t ≥ 0`. -/
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

/-- The production-decay formula equals `N0` at `t = 0`, for every real `P`,
`λ` and `N0`. For `λ = 0` this is an identity of the formula only (Lean's
`P/0 = 0`), not of the physical zero-decay solution `N0 + P*t`. -/
theorem production_decay_initial (P lam N0 : ℝ) :
    N0 * Real.exp (-lam * 0) + (P / lam) * (1 - Real.exp (-lam * 0)) = N0 := by
  simp

end EarthScience
