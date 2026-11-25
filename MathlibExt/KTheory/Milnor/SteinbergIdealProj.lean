/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.SteinbergSpanMul

/-!
# Degreewise refinement of the Steinberg ideal projection

The homogeneous quotient grading for Milnor `K`-theory is already established
structurally: `steinbergIdeal F` is homogeneous for `TensorRing.degree F` and
`MilnorKRing.degree` is defined as the generic two-sided quotient grade
`TwoSidedIdeal.quotientGrade` via `gradedAlgebraQuotientGrade`. This module
provides a finer degreewise description: the homogeneous projection of an
element of the Steinberg ideal lands not merely back in the ideal, but in the
explicit degreewise Steinberg insertion span `steinbergDegreeSpan`.

The proof uses that Steinberg generators lie in degree two, the ideal is
two-sided, and the generic antidiagonal formula
`GradedAlgebra.proj_mul_eq_sum_antidiagonal` for projections of products
preserves the span via `degree_mul_steinbergDegreeSpan_mem` and
`steinbergDegreeSpan_mul_degree_mem`.

## Main results

* `TensorRing.proj_mem_steinbergDegreeSpan_of_mem_steinbergIdeal`: for
  `x ∈ steinbergIdeal F`, its degree-`n` projection lies in
  `steinbergDegreeSpan F n`. This is strictly more precise than the generic
  homogeneity statement that the projection stays in the ideal.
-/

@[expose] public section

open Finset

namespace MilnorK

variable (F : Type*) [Field F]

namespace TensorRing

private lemma steinbergSet_mem_insertSet_two {y : TensorRing F}
    (hy : y ∈ steinbergSet F) : y ∈ steinbergInsertSet F 2 := by
  rcases hy with ⟨a, ha0, ha1, rfl⟩
  refine ⟨[], [], a, ha0, ha1, rfl, ?_⟩
  simp [tensorList_nil]

private lemma proj_steinbergSet_mem {y : TensorRing F}
    (hy : y ∈ steinbergSet F) (n : ℕ) :
    proj F n y ∈ steinbergDegreeSpan F n := by
  have hy_deg : y ∈ degree F 2 := steinbergSet_subset_degree_two F hy
  by_cases hEq : n = 2
  · subst hEq
    have hproj : proj F 2 y = y :=
      GradedAlgebra.proj_eq_self (𝒜 := degree F) hy_deg
    rw [hproj]
    have hIns : y ∈ steinbergInsertSet F 2 :=
      steinbergSet_mem_insertSet_two (F := F) hy
    exact Submodule.subset_span hIns
  · have hNe : (2 : ℕ) ≠ n := fun h => hEq h.symm
    have hZero : proj F n y = 0 :=
      GradedAlgebra.proj_eq_zero_of_ne (𝒜 := degree F) hy_deg hNe
    rw [hZero]
    exact Submodule.zero_mem _

/-- If `x` lies in the Steinberg ideal, its homogeneous component in degree `n`
lies in the degreewise Steinberg span. This is a degreewise refinement of the
structural quotient grading: the quotient is already graded via the general
homogeneous two-sided ideal machinery, while this theorem exhibits the explicit
span containing the projected ideal elements. -/
theorem proj_mem_steinbergDegreeSpan_of_mem_steinbergIdeal
    {x : TensorRing F} (hx : x ∈ steinbergIdeal F) (n : ℕ) :
    proj F n x ∈ steinbergDegreeSpan F n := by
  have hall : ∀ m, proj F m x ∈ steinbergDegreeSpan F m := by
    refine TwoSidedIdeal.span_induction (s := steinbergSet F) ?_ ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy m
      exact proj_steinbergSet_mem (F := F) hy m
    · intro m
      have : proj F m (0 : TensorRing F) = 0 := by simp
      rw [this]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb m
      have hAdd : proj F m (a + b) = proj F m a + proj F m b := by
        simp [map_add]
      rw [hAdd]
      exact Submodule.add_mem _ (ha m) (hb m)
    · intro a _ ha m
      have hNeg : proj F m (-a) = - proj F m a := by
        simp [map_neg]
      rw [hNeg]
      exact Submodule.neg_mem _ (ha m)
    · intro a x _ hx m
      have hEq : proj F m (a * x) =
          ∑ ij ∈ antidiagonal m, proj F ij.1 a * proj F ij.2 x :=
        GradedAlgebra.proj_mul_eq_sum_antidiagonal
          (𝒜 := degree F) a x m
      rw [hEq]
      apply Submodule.sum_mem
      intro ij hij
      have hij_sum : ij.1 + ij.2 = m := by
        rwa [Finset.mem_antidiagonal] at hij
      have ha_deg : proj F ij.1 a ∈ degree F ij.1 :=
        GradedAlgebra.proj_mem (𝒜 := degree F) ij.1 a
      have hx_span : proj F ij.2 x ∈ steinbergDegreeSpan F ij.2 := hx ij.2
      have hMul : proj F ij.1 a * proj F ij.2 x ∈
          steinbergDegreeSpan F (ij.1 + ij.2) :=
        degree_mul_steinbergDegreeSpan_mem F ha_deg hx_span
      have : ij.1 + ij.2 = m := hij_sum
      rw [this] at hMul
      exact hMul
    · intro b x _ hx m
      have hEq : proj F m (x * b) =
          ∑ ij ∈ antidiagonal m, proj F ij.1 x * proj F ij.2 b :=
        GradedAlgebra.proj_mul_eq_sum_antidiagonal
          (𝒜 := degree F) x b m
      rw [hEq]
      apply Submodule.sum_mem
      intro ij hij
      have hij_sum : ij.1 + ij.2 = m := by
        rwa [Finset.mem_antidiagonal] at hij
      have hx_span : proj F ij.1 x ∈ steinbergDegreeSpan F ij.1 := hx ij.1
      have hb_deg : proj F ij.2 b ∈ degree F ij.2 :=
        GradedAlgebra.proj_mem (𝒜 := degree F) ij.2 b
      have hMul : proj F ij.1 x * proj F ij.2 b ∈
          steinbergDegreeSpan F (ij.1 + ij.2) :=
        steinbergDegreeSpan_mul_degree_mem F hx_span hb_deg
      have : ij.1 + ij.2 = m := hij_sum
      rw [this] at hMul
      exact hMul
  exact hall n

end TensorRing

end MilnorK
