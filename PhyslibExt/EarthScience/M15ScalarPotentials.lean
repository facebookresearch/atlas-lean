/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
/-!
# Scalar potentials: derivatives of a quadratic profile

For a quadratic potential `φ(x) = a*x^2 + b*x + c`, the first derivative
is `2*a*x + b` and the second derivative is the constant `2*a`.

## i. Overview

This file proves the two derivative facts for the quadratic profile named
in the Atlas roadmap item M15. The second-derivative statement is phrased
as a `HasDerivAt` statement about the first-derivative function
`x ↦ 2*a*x + b`, whose derivative is the constant `2*a`; no claim is made
about harmonicity of the singular potential `1/r` on `ℝ^3 ∖ {0}`, which is
a separate target pending a canonical Laplacian API audit and is not
attempted here.

## ii. Key results

- `EarthScience.quadratic_hasDerivAt`: `φ` has derivative `2*a*x + b` at `x`.
- `EarthScience.quadratic_second_hasDerivAt`: the derivative function has
  derivative `2*a` at `x`, i.e. `φ''(x) = 2*a`.

## iii. References

- `hasDerivAt_pow`, `HasDerivAt.const_mul`, `HasDerivAt.add_const` in
  Mathlib (`Mathlib/Analysis/Calculus/Deriv/`).
-/

@[expose] public section

namespace EarthScience

/-- First derivative of a quadratic potential `φ(x) = a*x^2 + b*x + c`. -/
theorem quadratic_hasDerivAt (a b c x : ℝ) :
    HasDerivAt (fun x => a * x ^ 2 + b * x + c) (2 * a * x + b) x := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun x : ℝ => a * x ^ 2) (a * (2 * x)) x :=
    hpow.const_mul a
  have h2 : HasDerivAt (fun x : ℝ => b * x) b x := by
    simpa using (hasDerivAt_id' x).const_mul b
  have h := (h1.add h2).add_const c
  convert h using 1
  ring

/-- Second derivative of a quadratic potential: the derivative function
`x ↦ 2*a*x + b` has constant derivative `2*a`, so `φ''(x) = 2*a`. -/
theorem quadratic_second_hasDerivAt (a b x : ℝ) :
    HasDerivAt (fun x => 2 * a * x + b) (2 * a) x := by
  simpa using ((hasDerivAt_id' x).const_mul (2 * a)).add_const b

end EarthScience
