/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.CapacityNonneg

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.CapacityNonneg`

* `ShrinksIm` for the identity and for the half-disk maps `z ↦ z + c/z`, `c ≥ 0`.
* `hcap_nonneg_of_shrinksIm` instantiated with `z ↦ z + 1/z` (capacity `1`).
* `le_of_comp_of_shrinksIm` with `g = id`, `h = z ↦ z + 1/z`.
-/

@[expose] public section

open StatMech.SLE Complex

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.CapacityNonneg

example : ShrinksIm id := fun _ _ => le_rfl

example : ShrinksIm (fun z : ℂ => z + ((1 : ℝ) : ℂ) / z) := shrinksIm_halfDisk zero_le_one

example : (0 : ℝ) ≤ 1 :=
  hcap_nonneg_of_shrinksIm (hasHalfPlaneCapacity_halfDisk 1) (shrinksIm_halfDisk zero_le_one)

example : (0 : ℝ) ≤ 1 :=
  le_of_comp_of_shrinksIm (g := id) hasHalfPlaneCapacity_id (hasHalfPlaneCapacity_halfDisk 1)
    (shrinksIm_halfDisk zero_le_one) rfl (by simpa using hasHalfPlaneCapacity_halfDisk 1)

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.CapacityNonneg
