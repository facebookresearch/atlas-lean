/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
/-!
# Arrhenius law is increasing in temperature

An admissible Arrhenius law `k(T) = A * exp(-Ea / (R * T))` with
`A > 0`, `Ea > 0`, `R > 0` is positive for `T > 0` and strictly
increasing in `T` on `(0, ∞)`.

## i. Overview

As `T` grows, `R * T` grows, so `Ea / (R * T)` falls, `-Ea / (R * T)`
rises, and `exp` preserves the order; multiplying by `A > 0` preserves
it again. Positive activation energy is essential: at `Ea = 0` the law
is constant.

## ii. Key results

- `EarthScience.arrhenius_pos`: `k(T) > 0` for `T > 0`.
- `EarthScience.arrhenius_strictMonoOn`: `k` is strictly increasing on
  `(0, ∞)` for `Ea > 0`.

## iii. References

- `Real.exp_pos`, `Real.exp_strictMono`, `div_lt_div_of_pos_left`,
  `mul_lt_mul_of_pos_left` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- An admissible Arrhenius law `k(T) = A * exp(-Ea / (R * T))` is positive
for `T > 0` when `A > 0`. -/
theorem arrhenius_pos {A Ea R : ℝ} (hA : 0 < A)
    {T : ℝ} (hT : 0 < T) :
    0 < A * Real.exp (-Ea / (R * T)) := by
  have _ := hT
  exact mul_pos hA (Real.exp_pos _)

/-- An admissible Arrhenius law is strictly increasing in `T` on `(0, ∞)`
for positive activation energy `Ea > 0` and `A > 0`, `R > 0`. -/
theorem arrhenius_strictMonoOn {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T : ℝ => A * Real.exp (-Ea / (R * T))) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have hRx : 0 < R * x := mul_pos hR hx
  have hRxy : R * x < R * y := mul_lt_mul_of_pos_left hxy hR
  have hE : Ea / (R * y) < Ea / (R * x) := div_lt_div_of_pos_left hEa hRx hRxy
  have hneg : -Ea / (R * x) < -Ea / (R * y) := by
    rw [neg_div, neg_div]
    exact neg_lt_neg hE
  have hexp : Real.exp (-Ea / (R * x)) < Real.exp (-Ea / (R * y)) :=
    Real.exp_strictMono hneg
  exact mul_lt_mul_of_pos_left hexp hA

end EarthScience
