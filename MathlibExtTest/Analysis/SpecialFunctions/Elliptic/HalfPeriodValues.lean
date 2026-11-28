/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.HalfPeriodValues

@[expose] public section

namespace PeriodPair

open scoped PeriodPair

/-- `℘'` vanishes at the half-period `(ω₁ + ω₂) / 2`. -/
example (L : PeriodPair) : ℘'[L] ((L.ω₁ + L.ω₂) / 2) = 0 :=
  (L.half_period_values _ (by simp)).2.1

/-- `℘(ω₁ / 2)` is a root of `4 X³ - g₂ X - g₃`. -/
example (L : PeriodPair) :
    4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) - L.g₃ = 0 :=
  (L.half_period_values _ (by simp)).2.2

example (L : PeriodPair) : L.ω₂ / 2 ∉ L.lattice :=
  (L.half_period_values _ (by simp)).1

end PeriodPair
