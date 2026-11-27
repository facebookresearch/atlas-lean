/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.LegendreJ

@[expose] public section

open ModularCurve

/-- Consumer with the original binders. -/
private theorem exactSource {K : Type*} [Field K] (t : K) :
    legendreJ t⁻¹ = legendreJ t :=
  ModularCurve.legendreJ_inv t

-- The totalized statement also holds at `t = 0`, where both sides are `0`.
example {K : Type*} [Field K] : legendreJ (0 : K)⁻¹ = legendreJ (0 : K) :=
  ModularCurve.legendreJ_inv 0

-- Inverting twice returns the original value, as a boundary check.
example {K : Type*} [Field K] (t : K) : legendreJ t⁻¹⁻¹ = legendreJ t := by
  rw [ModularCurve.legendreJ_inv, ModularCurve.legendreJ_inv]
