/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverageDegenerateSecondOrderSums

/-! # Tests for sums of degenerate second-order recurrences -/

namespace MathlibExtTest.NumberTheory.Recurrences.LucasPeriodAverageDegenerateSecondOrderSums

-- The `U(0, -1)` partial sums count odd indices: the first five sum to three.
example : ∑ i ∈ Finset.Icc 1 5, MetaMathlibExt.lucasU ⟨0, -1, by decide⟩ i = 3 := by
  obtain ⟨c1, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    MetaMathlibExt.degenerate_secondOrder_sums
  have h := c1 5 (by decide)
  have h2 : ((((5 + 1) / 2 : ℕ)) : ℤ) = 3 := by decide
  rw [h2] at h
  exact h

-- The `U(-2, 1)` partial sums alternate in sign: the first four sum to `-2`.
example : ∑ i ∈ Finset.Icc 1 4, MetaMathlibExt.lucasU ⟨-2, 1, by decide⟩ i = -2 := by
  obtain ⟨-, -, -, -, -, -, -, -, c9, -, -, -⟩ :=
    MetaMathlibExt.degenerate_secondOrder_sums
  have h := c9 4 (by decide)
  have h2 : (-1 : ℤ) ^ (4 + 1) * ((((4 + 1) / 2 : ℕ)) : ℤ) = -2 := by decide
  rw [h2] at h
  exact h

-- Three has integral averages for arithmetic progressions since it is odd.
example : MetaMathlibExt.lucasAllAveragesIntegral ⟨2, 1, by decide⟩ 3 := by
  obtain ⟨-, -, -, -, -, -, c7, -, -, -, -, -⟩ :=
    MetaMathlibExt.degenerate_secondOrder_sums
  exact (c7 3 (by decide)).mpr ⟨1, by decide⟩

-- A constant sequence sums to its length times its value.
example : ∑ i ∈ Finset.Icc 1 4, (fun _ : ℕ => (7 : ℤ)) i = 28 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, c11, -⟩ :=
    MetaMathlibExt.degenerate_secondOrder_sums
  have hw : ∀ k, (fun _ : ℕ => (7 : ℤ)) (k + 2) = (fun _ : ℕ => (7 : ℤ)) (k + 1) :=
    fun _ => rfl
  have h := c11 (fun _ : ℕ => (7 : ℤ)) hw 4
  have h2 : ((4 : ℕ) : ℤ) * 7 = 28 := by decide
  rw [h2] at h
  exact h

end MathlibExtTest.NumberTheory.Recurrences.LucasPeriodAverageDegenerateSecondOrderSums
