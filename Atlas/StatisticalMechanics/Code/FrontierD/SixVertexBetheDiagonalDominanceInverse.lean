/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.LinearAlgebra.Matrix.Gershgorin









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem diagonalMargin_mul_abs_le_abs_mulVec
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) (x : n -> Real) (i : n) {delta : Real}
    (hmax : forall j, |x j| <= |x i|)
    (hmargin : delta + (∑ j ∈ univ.erase i, |A i j|) <= |A i i|) :
    delta * |x i| <= |A.mulVec x i| := by
  let off : Real := ∑ j ∈ univ.erase i, A i j * x j
  have hrow : A.mulVec x i = A i i * x i + off := by
    rw [Matrix.mulVec, dotProduct]
    change (∑ j, A i j * x j) = _
    rw [<- sum_erase_add _ _ (mem_univ i)]
    dsimp [off]
    ring_nf
  have hoff : |off| <= (∑ j ∈ univ.erase i, |A i j|) * |x i| := by
    calc
      |off| <= ∑ j ∈ univ.erase i, |A i j * x j| :=
        abs_sum_le_sum_abs _ _
      _ <= ∑ j ∈ univ.erase i, |A i j| * |x i| := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
      _ = (∑ j ∈ univ.erase i, |A i j|) * |x i| := by
        rw [sum_mul]
  have hdiag : delta * |x i| +
      (∑ j ∈ univ.erase i, |A i j|) * |x i| <=
        |A i i| * |x i| := by
    rw [<- add_mul]
    exact mul_le_mul_of_nonneg_right hmargin (abs_nonneg _)
  have htriangle : |A i i| * |x i| <= |A.mulVec x i| + |off| := by
    rw [<- abs_mul, hrow]
    calc
      |A i i * x i| = |(A i i * x i + off) - off| := by ring_nf
      _ <= |A i i * x i + off| + |off| := abs_sub _ _
  linarith




theorem exists_abs_le_abs_mulVec_of_diagonalMargin
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n Real) (x : n -> Real) {delta : Real}
    (hmargin : forall i,
      delta + (∑ j ∈ univ.erase i, |A i j|) <= |A i i|) :
    exists i, (forall j, |x j| <= |x i|) /\
      delta * |x i| <= |A.mulVec x i| := by
  classical
  obtain ⟨i, hi⟩ := Finset.exists_max_image univ (fun j => |x j|)
    (Finset.univ_nonempty : univ.Nonempty)
  refine ⟨i, ?_, diagonalMargin_mul_abs_le_abs_mulVec A x i ?_ (hmargin i)⟩
  · intro j
    exact hi.2 j (mem_univ j)
  · intro j
    exact hi.2 j (mem_univ j)

end

end StatMech.FrontierD
