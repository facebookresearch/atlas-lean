/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_legendreJ_inv.lean`,
`Definitions/Def_ModularCurve_LegendreJ.lean` and
`P2M/Sol/S_ModularCurve_legendreJ_inv.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace ModularCurve

/-- The Legendre form of the `j`-invariant: for a parameter `t` in a field
`K`, `legendreJ t = 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)`,
with division totalized in the usual way for fields. -/
public def legendreJ {K : Type*} [Field K] (t : K) : K :=
  2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

/-- The defining formula for the Legendre `j`-invariant. -/
public theorem legendreJ_apply {K : Type*} [Field K] (t : K) :
    legendreJ t = 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2) :=
  rfl

/-- The Legendre `j`-invariant is unchanged by inverting the parameter:
`legendreJ t⁻¹ = legendreJ t` for every `t` in a field, with inversion
and division totalized. -/
public theorem legendreJ_inv {K : Type*} [Field K] (t : K) :
    legendreJ t⁻¹ = legendreJ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [inv_zero]
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hu : (t⁻¹ : K) ≠ 0 := inv_ne_zero ht
  have e1 : (t⁻¹ ^ 2 - t⁻¹ + 1) ^ 3 = (t ^ 2 - t + 1) ^ 3 * t⁻¹ ^ 6 := by
    linear_combination
      (-t ^ 5 * t⁻¹ ^ 5 + 3 * t ^ 4 * t⁻¹ ^ 5 - t ^ 4 * t⁻¹ ^ 4
        - 6 * t ^ 3 * t⁻¹ ^ 5 + 3 * t ^ 3 * t⁻¹ ^ 4 - t ^ 3 * t⁻¹ ^ 3
        + 7 * t ^ 2 * t⁻¹ ^ 5 - 6 * t ^ 2 * t⁻¹ ^ 4 + 3 * t ^ 2 * t⁻¹ ^ 3
        - t ^ 2 * t⁻¹ ^ 2 - 6 * t * t⁻¹ ^ 5 + 7 * t * t⁻¹ ^ 4
        - 6 * t * t⁻¹ ^ 3 + 3 * t * t⁻¹ ^ 2 - t * t⁻¹ + 3 * t⁻¹ ^ 5
        - 6 * t⁻¹ ^ 4 + 7 * t⁻¹ ^ 3 - 6 * t⁻¹ ^ 2 + 3 * t⁻¹ - 1) * hi
  have e2 : t⁻¹ ^ 2 * (t⁻¹ - 1) ^ 2 = (t ^ 2 * (t - 1) ^ 2) * t⁻¹ ^ 6 := by
    linear_combination
      (-t ^ 3 * t⁻¹ ^ 5 + 2 * t ^ 2 * t⁻¹ ^ 5 - t ^ 2 * t⁻¹ ^ 4
        - t * t⁻¹ ^ 5 + 2 * t * t⁻¹ ^ 4 - t * t⁻¹ ^ 3 - t⁻¹ ^ 4
        + 2 * t⁻¹ ^ 3 - t⁻¹ ^ 2) * hi
  simp only [legendreJ]
  rw [e1, e2, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero 6 hu)]

end ModularCurve
