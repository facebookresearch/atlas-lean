/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentityFiber

/-!
# The fundamental identity for places of function fields

This file proves the fundamental identity `∑ e(w | v) f(w | v) = [F' : F]`, where `w` runs over the
places of a finite separable extension `F'` restricting to a place `v` of `F`.

When every nonzero element of `F'` has a principal divisor, the places of `F'` over `v` form the
finset `v.fiber F'`, which equals `v.fiberOver F'` (`AlgebraicCurve.Place.fiber_eq_fiberOver`), so
the identity is `AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` rewritten.

## Main statement

* `AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg`
-/

namespace AlgebraicCurve.Place

/-- The fundamental identity: for a finite separable extension `F'` of `F` and a place `v` of `F`,
the sum of `e(w | v) f(w | v)` over the places `w` above `v` is `[F' : F]`. -/
public theorem sum_ramificationIndex_mul_inertiaDeg
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [HasPrincipalDivisors K F'] (v : Place K F) :
    ∑ w ∈ v.fiber F',
        (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) = (Module.finrank F F' : ℤ) := by
  rw [v.fiber_eq_fiberOver]
  exact v.sum_ramificationIndex_mul_inertiaDeg_fiberOver

end AlgebraicCurve.Place
