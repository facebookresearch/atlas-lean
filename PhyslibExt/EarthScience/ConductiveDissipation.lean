/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Conductive dissipation is nonnegative

## i. Overview

With nonnegative conductivity `k`, the conductive dissipation is
nonnegative: pointwise, the dissipation density `k * (T'(z)) ^ 2` is a
nonnegative multiple of a square, and integrated over an interval
`[a, b]`, `∫ z in a..b, k * (T'(z)) ^ 2 ≥ 0`. The statement is about
conduction in a temperature profile `T`, with `deriv` the ordinary
one-dimensional derivative; it does not assume `T` satisfies a PDE or
any boundary conditions. (The diffusive-energy module proves the
negated dissipation term `-D * ∫ c_x ^ 2 ≤ 0` for a periodic PDE; the
nonnegativity of the conductive dissipation itself was not stated
there.)

## ii. Key results

- `EarthScience.conductive_dissipation_nonneg`: pointwise and
  integrated conductive dissipation are nonnegative for `k ≥ 0`.

## iii. Table of contents

- A. Nonnegative conductive dissipation

## iv. References

- `mul_nonneg`, `sq_nonneg` in Mathlib.
- `intervalIntegral.integral_nonneg_of_forall` in Mathlib.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-! ## A. Nonnegative conductive dissipation -/

set_option linter.unusedVariables false in
/-- With nonnegative conductivity `k`, the conductive dissipation is
nonnegative: pointwise, `0 ≤ k * (T'(z))^2`, and integrated over
`[a, b]`, `0 ≤ ∫ z in a..b, k * (T'(z))^2`. -/
theorem conductive_dissipation_nonneg
    {k : ℝ} (hk : 0 ≤ k) {T : ℝ → ℝ} {a b z : ℝ} (hab : a ≤ b)
    (hInt : IntervalIntegrable (fun z => k * (deriv T z) ^ 2) volume a b) :
    0 ≤ k * (deriv T z) ^ 2 ∧
    0 ≤ ∫ z in a..b, k * (deriv T z) ^ 2 := by
  exact ⟨mul_nonneg hk (sq_nonneg _),
    intervalIntegral.integral_nonneg_of_forall hab
      (fun _ => mul_nonneg hk (sq_nonneg _))⟩

end EarthScience
