/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.ErdosProblem755
import Mathlib.Tactic.NormNum

/-! # Tests for the equilateral triangle counts in Erdős Problem 755 -/

namespace MathlibExt.Geometry.ErdosProblem755Wanted.Tests

open Finset

private noncomputable def point (i : Fin 3) : EuclideanSpace ℝ (Fin 6) :=
  PiLp.single 2 (Fin.castLE (by decide : 3 ≤ 6) i) 1

private theorem point_dist {i j : Fin 3} (h : i ≠ j) :
    dist (point i) (point j) = Real.sqrt 2 := by
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num), EuclideanSpace.dist_sq_eq]
  have step (k : Fin 6) :
      dist (point i k) (point j k) ^ 2 =
        (if k = Fin.castLE (by decide : 3 ≤ 6) i then (1 : ℝ) else 0) +
        (if k = Fin.castLE (by decide : 3 ≤ 6) j then (1 : ℝ) else 0) := by
    have hn : Fin.castLE (by decide : 3 ≤ 6) i ≠ Fin.castLE (by decide : 3 ≤ 6) j :=
      fun he => h (Fin.ext (congrArg (Fin.val : Fin 6 → ℕ) he))
    by_cases hi : k = Fin.castLE (by decide : 3 ≤ 6) i
    · simp [point, hi, hn, PiLp.single_apply]
    · by_cases hj : k = Fin.castLE (by decide : 3 ≤ 6) j
      · simp [point, hj, hn.symm, PiLp.single_apply, Real.dist_eq]
      · simp [point, hi, hj]
  simp_rw [step]
  rw [sum_add_distrib]
  norm_num

private theorem point_injective : Function.Injective point := by
  intro i j h
  by_contra hn
  have hd := point_dist hn
  rw [h, dist_self] at hd
  exact (Real.sqrt_pos.2 (by norm_num)).ne' hd.symm

open scoped Classical in
private noncomputable def sample : Finset (EuclideanSpace ℝ (Fin 6)) := univ.image point

private theorem sample_card : sample.card = 3 := by
  classical
  simp [sample, card_image_of_injective _ point_injective]

private theorem sample_triangles : sample.powersetCard 3 = {sample} := by
  rw [← sample_card, powersetCard_self]

-- The coordinate unit vectors form one triangle, of side length √2.
example : anySizeEquilateralTriangleCount 6 sample = 1 := by
  classical
  have he : IsAnySizeEquilateralTriangle sample := by
    refine ⟨Real.sqrt 2, Real.sqrt_pos.2 (by norm_num), sample_card, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    exact point_dist (fun h => hxy (congrArg point h))
  rw [anySizeEquilateralTriangleCount, sample_triangles]
  apply card_eq_one.mpr
  refine ⟨sample, ?_⟩
  ext t
  simp only [mem_filter, mem_singleton]
  exact ⟨And.left, fun ht => ⟨ht, ht.symm ▸ he⟩⟩

example : unitEquilateralTriangleCount 6 sample = 0 := by
  classical
  have he : ¬ IsUnitEquilateralTriangle sample := by
    intro h
    have hdist := h.2 (point 0) (mem_image_of_mem _ (mem_univ _))
      (point 1) (mem_image_of_mem _ (mem_univ _))
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (point_injective he))
    rw [point_dist (by decide : (0 : Fin 3) ≠ 1)] at hdist
    have hsq := congrArg (fun x : ℝ => x ^ 2) hdist
    norm_num [Real.sq_sqrt] at hsq
  simp [unitEquilateralTriangleCount, sample_triangles, he]

example : TAnySize 6 2 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro m ⟨P, hP, rfl⟩
  have h : (P.powersetCard 3).card = 0 := by simp [hP]
  exact (card_filter_le _ _).trans_eq h

end MathlibExt.Geometry.ErdosProblem755Wanted.Tests
