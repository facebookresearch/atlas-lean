/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PathTracing
public import Mathlib.Basic.Real.Basic

/-!
# Tests for path tracing

For `B = !![0, 0, 0; 2, 0, 0; 5, 3, 0]` (edges `0 → 1` with coefficient `2`, `1 → 2` with `3`,
`0 → 2` with `5`), path tracing gives `((1 - B)⁻¹) 2 0 = 5 + 3 * 2 = 11` and
`((1 - B)⁻¹) 0 2 = 0` (no path from `2` to `0`).
-/

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.PathTracing

open _root_.Matrix

section PathTracingTest

private theorem test_hB : ∀ i j : Fin 3, i ≤ j →
    (!![0, 0, 0; 2, 0, 0; 5, 3, 0] : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem test_sort02 :
    ((({0, 2} : Finset (Fin 3)).sort (fun a b => a ≤ b))) = [0, 2] := by
  have h := Finset.sort_insert (fun a b => a ≤ b)
    (s := ({2} : Finset (Fin 3))) (a := 0)
    (fun b hb => by simp at hb; subst hb; decide) (by decide)
  rwa [Finset.sort_singleton] at h

private theorem test_sort012 :
    ((({0, 1, 2} : Finset (Fin 3)).sort (fun a b => a ≤ b))) = [0, 1, 2] := by
  have h1 := Finset.sort_insert (fun a b => a ≤ b)
    (s := ({2} : Finset (Fin 3))) (a := 1)
    (fun b hb => by simp at hb; subst hb; decide) (by decide)
  rw [Finset.sort_singleton] at h1
  have h0 := Finset.sort_insert (fun a b => a ≤ b)
    (s := ({1, 2} : Finset (Fin 3))) (a := 0)
    (fun b hb => by fin_cases b <;> simp_all) (by decide)
  have heq : ({0, 1, 2} : Finset (Fin 3)) = insert 0 {1, 2} := rfl
  rw [heq, h0, h1]

private theorem test_paths : increasingPaths (0 : Fin 3) 2
    = ({[0, 2], [0, 1, 2]} : Finset (List (Fin 3))) := by
  ext p
  rw [increasingPaths_eq_filter_univ]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨S, ⟨h0S, h2S, hbS⟩, rfl⟩
    have hSeq : S = {0, 2} ∨ S = ({0, 1, 2} : Finset (Fin 3)) := by
      by_cases h1 : (1 : Fin 3) ∈ S
      · right; ext x; fin_cases x <;> simp_all
      · left; ext x; fin_cases x <;> simp_all
    rcases hSeq with rfl | rfl
    · exact Or.inl test_sort02
    · exact Or.inr test_sort012
  · rintro (rfl | rfl)
    · refine ⟨{0, 2}, ⟨by decide, by decide, ?_⟩, test_sort02⟩
      intro k hk
      fin_cases k <;> decide
    · refine ⟨{0, 1, 2}, ⟨by decide, by decide, ?_⟩, test_sort012⟩
      intro k hk
      fin_cases k <;> decide

example : ((1 - !![0, 0, 0; 2, 0, 0; 5, 3, 0])⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 11 := by
  rw [inv_one_sub_apply_eq_sum_pathWeight test_hB, test_paths,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [pathWeight]
  norm_num

example : ((1 - !![0, 0, 0; 2, 0, 0; 5, 3, 0])⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 := by
  rw [inv_one_sub_apply_eq_sum_pathWeight test_hB,
    increasingPaths_empty_of_not_le (by decide : ¬ (2 : Fin 3) ≤ 0)]
  exact Finset.sum_empty

end PathTracingTest

end MathlibExtTest.LinearAlgebra.Matrix.PathTracing
