/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Discrete model verification: periodic first-order upwind

The periodic first-order upwind update
`c⁺ i = (1 - ν) c i + ν c (i - 1)` on `ZMod n` (periodic cells, `i - 1`
the upstream neighbour) preserves nonnegativity under the CFL condition
`0 ≤ ν ≤ 1` and preserves the total sum for every `ν`.

## i. Overview

Nonnegativity is pointwise: each updated cell is a convex combination of
two nonnegative values. The total sum is preserved because the periodic
shift `i ↦ i - 1` permutes the cells, so the `ν` terms cancel in the sum.
These are exact-real identities; floating-point roundoff is separate.

## ii. Key results

- `EarthScience.upwind_nonneg`: the CFL condition preserves
  nonnegativity.
- `EarthScience.upwind_sum_eq`: the total sum is preserved for every `ν`.

## iii. Table of contents

- A. Upwind nonnegativity and conservation

## iv. References

- `Equiv.sum_comp` in
  `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (Mathlib).

## A. Upwind nonnegativity and conservation
-/

@[expose] public section

namespace EarthScience

/-- Periodic first-order upwind update preserves nonnegativity under the
CFL condition `0 ≤ ν ≤ 1`: with `c⁺ i = (1 - ν) * c i + ν * c (i - 1)` on
`ZMod n` (periodic cells, `i - 1` the upstream neighbour), every updated
cell is nonnegative when every `c i` is. -/
theorem upwind_nonneg {n : ℕ} [NeZero n] (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (c : ZMod n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ (1 - ν) * c i + ν * c (i - 1) := by
  intro i
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hν1) (hc i)) (mul_nonneg hν0 (hc (i - 1)))

/-- Periodic first-order upwind update preserves the total sum for every
`ν`: the sum of the updated cells equals the sum of the old cells, because
the periodic shift `i ↦ i - 1` permutes the cells. -/
theorem upwind_sum_eq {n : ℕ} [NeZero n] (ν : ℝ) (c : ZMod n → ℝ) :
    ∑ i, ((1 - ν) * c i + ν * c (i - 1)) = ∑ i, c i := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : (∑ i, c (i - 1)) = ∑ i, c i := by
    have h2 := Equiv.sum_comp (Equiv.subRight (1 : ZMod n)) c
    simpa using h2
  rw [h]
  ring

end EarthScience
