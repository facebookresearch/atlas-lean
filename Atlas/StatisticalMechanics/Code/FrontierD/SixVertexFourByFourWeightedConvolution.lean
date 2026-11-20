/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexFourByFourRowCycleBase

open Finset

namespace StatMech.FrontierD

theorem fintypeWeightedGradeConvolution
    {A B : Type*} [Fintype A] [Fintype B]
    (gradeA : A → Nat) (gradeB : B → Nat)
    (weightA : A → Nat) (weightB : B → Nat) (total : Nat) :
    (∑ a, ∑ b,
      if gradeA a + gradeB b = total then weightA a * weightB b else 0) =
      ∑ k : Fin (total + 1),
        (∑ a, if gradeA a = k.val then weightA a else 0) *
          (∑ b, if gradeB b = total - k.val then weightB b else 0) := by
  symm
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hsum : gradeA a + gradeB b = total
  · rw [if_pos hsum]
    let k : Fin (total + 1) := ⟨gradeA a, by omega⟩
    rw [Fintype.sum_eq_single k]
    · have hsecond : gradeB b = total - gradeA a := by omega
      simp [k, hsecond]
    · intro other hne
      have hgrade : gradeA a ≠ other.val := by
        intro heq
        apply hne
        apply Fin.ext
        exact heq.symm
      simp [hgrade]
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hfirst : gradeA a = k.val
    · have hsecond : gradeB b ≠ total - k.val := by
        intro heq
        apply hsum
        rw [hfirst, heq]
        omega
      simp [hsecond]
    · simp [hfirst]

theorem sixVertexFourTableProduct_explicit
    (index0 index1 index2 index3 : Fin 16) :
    (∏ j, sixVertexFourHorizontalTransitionCount
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16)
          (SixVertexArrows.cyclicPred
            sixVertexFourByFourTorus.height_pos j))
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j)) =
      sixVertexFourHorizontalTransitionCount index3 index0 *
        sixVertexFourHorizontalTransitionCount index0 index1 *
        sixVertexFourHorizontalTransitionCount index1 index2 *
        sixVertexFourHorizontalTransitionCount index2 index3 := by
  let f : Fin 4 → Nat := fun j =>
    sixVertexFourHorizontalTransitionCount
      ((![index0, index1, index2, index3] : Fin 4 → Fin 16)
        (SixVertexArrows.cyclicPred
          sixVertexFourByFourTorus.height_pos j))
      ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j)
  change (∏ j, f j) = _
  calc
    _ = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f
    _ = _ := by rfl

end StatMech.FrontierD
