/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex

import Mathlib.Tactic.NormNum

/-!
# Tests for the Fredholm index of powers of the unilateral shift

* The shift has index `-1` and the backward shift has index `1`
  (over `ℂ`, and over `ℝ` for a power).
* The index formulas for powers: `S ^ 2` has index `-2`,
  `B ^ 3` has index `3`, and the zeroth powers have index `0`.
* The shift powers are Fredholm operators; `S ∘L B` is Fredholm of
  index `0`.
* Kernel and range characterizations in coordinates: a vector is in
  the range of `S` iff its `0`-th coordinate vanishes; it is in the
  kernel of `B` iff all coordinates from `1` onwards vanish.
* Dimension counts: `ker (B ^ 2)` and the cokernel of `S ^ 2` both
  have dimension `2`.
-/

open scoped _root_.lp

namespace MathlibExtTest.Analysis.InnerProductSpace.ShiftFredholmIndexTests

open MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-- The unilateral shift on `ℓ²(ℕ, ℂ)` has Fredholm index `-1`. -/
example : (shiftCLM (𝕜 := ℂ)).index = -1 :=
  index_shiftCLM

/-- The backward shift on `ℓ²(ℕ, ℂ)` has Fredholm index `1`. -/
example : (backwardCLM (𝕜 := ℂ)).index = 1 :=
  index_backwardCLM

/-- `S ^ 2` has Fredholm index `-2`. -/
example : (shiftCLM (𝕜 := ℂ) ^ 2).index = -2 :=
  index_shiftCLM_pow 2

/-- `B ^ 3` has Fredholm index `3`. -/
example : (backwardCLM (𝕜 := ℂ) ^ 3).index = 3 :=
  index_backwardCLM_pow 3

/-- `S ^ 0 = 1` has Fredholm index `0`. -/
example : (shiftCLM (𝕜 := ℂ) ^ 0).index = 0 := by
  simpa using index_shiftCLM_pow (𝕜 := ℂ) 0

/-- `B ^ 0 = 1` has Fredholm index `0`. -/
example : (backwardCLM (𝕜 := ℂ) ^ 0).index = 0 := by
  simpa using index_backwardCLM_pow (𝕜 := ℂ) 0

/-- The index formula also holds over `ℝ`: `S ^ 2` has index `-2`. -/
example : (shiftCLM (𝕜 := ℝ) ^ 2).index = -2 :=
  index_shiftCLM_pow 2

/-- The unilateral shift is a Fredholm operator. -/
example : (shiftCLM (𝕜 := ℂ) ^ 1).IsFredholm :=
  isFredholm_shiftCLM_pow 1

/-- The backward shift is a Fredholm operator. -/
example : (backwardCLM (𝕜 := ℂ) ^ 1).IsFredholm :=
  isFredholm_backwardCLM_pow 1

/-- `S ^ 2` is a Fredholm operator. -/
example : (shiftCLM (𝕜 := ℂ) ^ 2).IsFredholm :=
  isFredholm_shiftCLM_pow 2

/-- `B ^ 2` is a Fredholm operator. -/
example : (backwardCLM (𝕜 := ℂ) ^ 2).IsFredholm :=
  isFredholm_backwardCLM_pow 2

/-- `S ∘L B` is a Fredholm operator. -/
example : (shiftCLM (𝕜 := ℂ) ∘L backwardCLM (𝕜 := ℂ)).IsFredholm :=
  isFredholm_shift_comp_backward

/-- `S ∘L B` has Fredholm index `0`. -/
example : (shiftCLM (𝕜 := ℂ) ∘L backwardCLM (𝕜 := ℂ)).index = 0 :=
  index_shift_comp_backward

/-- A vector is in the range of `S` iff its `0`-th coordinate vanishes. -/
example (y : ℓ²(ℕ, ℂ)) : (∃ x, shiftCLM (𝕜 := ℂ) x = y) ↔ y 0 = 0 := by
  have h := mem_range_shiftCLM_pow (𝕜 := ℂ) 1 y
  rw [pow_one] at h
  rw [h]
  constructor
  · intro h'
    exact h' 0 (by norm_num)
  · intro h' i hi
    rw [Nat.lt_one_iff.mp hi]
    exact h'

/-- A vector is in the kernel of `B` iff its coordinates from `1`
onwards all vanish. -/
example (x : ℓ²(ℕ, ℂ)) :
    (backwardCLM (𝕜 := ℂ)) x = 0 ↔ ∀ j ≥ 1, x j = 0 := by
  have h := mem_ker_backwardCLM_pow (𝕜 := ℂ) 1 x
  rw [pow_one] at h
  rw [h]
  constructor
  · intro h' j hj
    have hj' := h' (j - 1)
    rwa [Nat.sub_add_cancel hj] at hj'
  · intro h' i
    exact h' (i + 1) (by omega)

/-- The kernel of `B ^ 2` has dimension `2`. -/
example :
    Module.finrank ℂ (↑(backwardCLM (𝕜 := ℂ) ^ 2) : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)).ker = 2 :=
  finrank_ker_backwardCLM_pow 2

/-- The cokernel of `S ^ 2` has dimension `2`. -/
example :
    Module.finrank ℂ
      (ℓ²(ℕ, ℂ) ⧸ (↑(shiftCLM (𝕜 := ℂ) ^ 2) : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)).range) = 2 :=
  finrank_quotient_range_shiftCLM_pow 2

end MathlibExtTest.Analysis.InnerProductSpace.ShiftFredholmIndexTests
