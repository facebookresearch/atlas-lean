/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib









open Finset Set

namespace StatMech




theorem Fintype.sum_le_mul_sum_of_injective
    {Alpha Beta : Type*} [Fintype Alpha] [Fintype Beta]
    (D : Alpha -> Beta) (hinj : Function.Injective D)
    (sourceWeight : Alpha -> Real) (targetWeight : Beta -> Real)
    (C : Real) (hC : 0 <= C)
    (htarget : forall b, 0 <= targetWeight b)
    (hpoint : forall a, sourceWeight a <= C * targetWeight (D a)) :
    (∑ a, sourceWeight a) <= C * ∑ b, targetWeight b := by
  classical
  let image : Set Beta := Set.range D
  let e : Alpha ≃ image := Equiv.ofInjective D hinj
  calc
    (∑ a, sourceWeight a) <= ∑ a, C * targetWeight (D a) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = C * ∑ a, targetWeight (D a) := by
      rw [Finset.mul_sum]
    _ = C * ∑ b : image, targetWeight b.1 := by
      congr 1
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = C * ∑ b ∈ Finset.univ.filter (fun b => b ∈ image),
        targetWeight b := by
      congr 1
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun b => b ∈ image))
        (by
          intro b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change b ∈ Set.range D ↔ b ∈ Set.range D
          rfl)
        targetWeight).symm
    _ <= C * ∑ b, targetWeight b := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [Finset.sum_filter] using
        (Finset.sum_le_sum fun b (_hb : b ∈ Finset.univ) => by
          by_cases hb : b ∈ image
          · simp [hb]
          · simpa [hb] using htarget b)

end StatMech
