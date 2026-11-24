/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.ErdosProblem755
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Finset
open scoped Real

namespace MathlibExt.Geometry.ErdosProblem755Wanted.Tests

private noncomputable def vertex (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single i 1

private theorem vertex_dist {i j : Fin 3} (h : i ≠ j) : dist (vertex i) (vertex j) = √2 := by
  rw [EuclideanSpace.dist_eq]
  fin_cases i <;> fin_cases j <;> first | contradiction |
    norm_num [vertex, Fin.sum_univ_three, PiLp.single_apply, Real.dist_eq]

-- The three coordinate unit vectors span exactly one triangle, of side √2.
example : let P := univ.image vertex
    anySizeEquilateralTriangleCount 3 P = 1 ∧ unitEquilateralTriangleCount 3 P = 0 := by
  classical
  intro P
  have hi : Function.Injective vertex := by
    intro i j heq
    by_contra hne
    have hd := vertex_dist hne
    rw [heq, dist_self] at hd
    exact (ne_of_gt (show 0 < √(2 : ℝ) by positivity)) hd.symm
  have hc : P.card = 3 := by simp [P, card_image_of_injective _ hi]
  have hany : IsAnySizeEquilateralTriangle P := by
    refine ⟨√2, by positivity, hc, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    exact vertex_dist (fun heq => hxy (congrArg vertex heq))
  have hunit : ¬ IsUnitEquilateralTriangle P := by
    intro hu
    have hd := hu.2 (vertex 0) (mem_image_of_mem _ (mem_univ _))
      (vertex 1) (mem_image_of_mem _ (mem_univ _)) (hi.ne (by decide))
    rw [vertex_dist (by decide : (0 : Fin 3) ≠ 1)] at hd
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [hd] at hs
    norm_num at hs
  have hsub : P.powersetCard 3 = {P} := by
    simpa only [hc] using powersetCard_self P
  simp [unitEquilateralTriangleCount, anySizeEquilateralTriangleCount, hsub, filter_singleton,
    hany, hunit]

-- There is no two-point configuration in dimension zero.
example : TAnySize 0 2 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro m ⟨P, hP, _⟩
  have := P.card_le_one_of_subsingleton
  omega

end MathlibExt.Geometry.ErdosProblem755Wanted.Tests
