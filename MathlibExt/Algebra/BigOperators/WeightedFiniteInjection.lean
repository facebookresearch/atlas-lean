/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Weighted sums along an injection

If `D : α → β` is injective between finite types, `sourceWeight a ≤ C · targetWeight (D a)` for all
`a`, `C ≥ 0` and `targetWeight ≥ 0`, then `∑ sourceWeight ≤ C · ∑ targetWeight`. This is a
specialization of `Finset.sum_le_sum_of_injOn`.

## Main results

* `StatMech.Fintype.sum_le_mul_sum_of_injective`.
-/

@[expose] public section

open Finset Set

namespace StatMech

/-- If `D` is injective, `sourceWeight a ≤ C · targetWeight (D a)` for all `a`, `C ≥ 0` and
`targetWeight ≥ 0`, then `∑ a, sourceWeight a ≤ C · ∑ b, targetWeight b`. A specialization of
`Finset.sum_le_sum_of_injOn`. -/
theorem Fintype.sum_le_mul_sum_of_injective
    {α β : Type*} [Fintype α] [Fintype β]
    (D : α → β) (hinj : Function.Injective D)
    (sourceWeight : α → ℝ) (targetWeight : β → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (htarget : ∀ b, 0 ≤ targetWeight b)
    (hpoint : ∀ a, sourceWeight a ≤ C * targetWeight (D a)) :
    (∑ a, sourceWeight a) ≤ C * ∑ b, targetWeight b := by
  classical
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum_of_injOn D hinj.injOn (Finset.subset_univ _) (fun a _ => hpoint a)
    (fun b _ _ => mul_nonneg hC (htarget b))

end StatMech
