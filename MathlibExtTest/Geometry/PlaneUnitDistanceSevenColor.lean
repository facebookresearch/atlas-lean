/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import MathlibExt.Geometry.PlaneUnitDistanceSevenColor

open EuclideanGeometry.SevenColorTiling

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def vertex : Plane := WithLp.toLp 2 ![2 / 5, 2 / 15 * Real.sqrt 3]

private lemma dist_vertex_sq (i : ℤ × ℤ) :
    dist vertex (center i) ^ 2 = 16 / 75 + 16 / 25 *
      ((i.1 ^ 2 + i.1 * i.2 + i.2 ^ 2 - i.1 - i.2 : ℤ) : ℝ) := by
  simp [vertex, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    center_zero, center_one]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  linear_combination (2 / 15 - 2 / 5 * (i.2 : ℝ)) ^ 2 * hs

-- Computing the squared distance to every actual lattice center gives exactly these three minima.
private lemma vertex_nearest_iff (i : ℤ × ℤ) :
    (∀ j, dist vertex (center i) ≤ dist vertex (center j)) ↔
      i = (0, 0) ∨ i = (1, 0) ∨ i = (0, 1) := by
  have hnonneg (a b : ℤ) : 0 ≤ a ^ 2 + a * b + b ^ 2 - a - b := by
    nlinarith only [Int.le_self_sq a, Int.le_self_sq b, Int.le_self_sq (a + b)]
  constructor
  · rcases i with ⟨a, b⟩
    intro h
    have hsq := (sq_le_sq₀ dist_nonneg dist_nonneg).2 (h (0, 0))
    have hOrigin : dist vertex (center (0, 0)) ^ 2 = 16 / 75 := by norm_num [dist_vertex_sq]
    rw [dist_vertex_sq (a, b), hOrigin] at hsq
    have hcast : (0 : ℝ) ≤ ((a ^ 2 + a * b + b ^ 2 - a - b : ℤ) : ℝ) := by
      exact_mod_cast hnonneg a b
    have hzero : a ^ 2 + a * b + b ^ 2 - a - b = 0 := by
      exact_mod_cast (show ((a ^ 2 + a * b + b ^ 2 - a - b : ℤ) : ℝ) = 0 by linarith)
    have ha : a * (a - 1) = 0 := by
      nlinarith only [hzero, Int.le_self_sq a, Int.le_self_sq b, Int.le_self_sq (a + b)]
    have hb : b * (b - 1) = 0 := by
      nlinarith only [hzero, Int.le_self_sq a, Int.le_self_sq b, Int.le_self_sq (a + b)]
    rcases mul_eq_zero.mp ha with h | h <;> rcases mul_eq_zero.mp hb with k | k
    · left
      exact Prod.ext h k
    · right; right
      exact Prod.ext h (by omega)
    · right; left
      exact Prod.ext (by omega) k
    · have ha' : a = 1 := by omega
      have hb' : b = 1 := by omega
      norm_num [ha', hb'] at hzero
  · intro hi j
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
    have he : dist vertex (center i) ^ 2 = 16 / 75 := by
      rcases hi with rfl | rfl | rfl <;> norm_num [dist_vertex_sq]
    rw [he, dist_vertex_sq]
    have hcast : (0 : ℝ) ≤ ((j.1 ^ 2 + j.1 * j.2 + j.2 ^ 2 - j.1 - j.2 : ℤ) : ℝ) := by
      exact_mod_cast hnonneg j.1 j.2
    linarith

-- The lattice color really wraps at seven, and adjacent centers need not have the same color.
example : residue (1, 2) = residue (0, 0) ∧ residue (1, 0) ≠ residue (0, 0) ∧
    dist (center (1, 2)) (center (0, 0)) ^ 2 = 112 / 25 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Fin.ext
    norm_num [residue_val]
  · intro h
    have hc := congrArg Fin.val h
    norm_num [residue_val] at hc
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
      center_zero, center_one]
    norm_num
    nlinarith only [hs]

-- Any tie-break at the vertex must choose one of the three actual lattice colors.
example : sevenColor vertex = 0 ∨ sevenColor vertex = 1 ∨ sevenColor vertex = 3 := by
  rw [sevenColor_eq]
  have h := (vertex_nearest_iff (nearestCenter vertex)).1 (nearestCenter_spec vertex)
  rcases h with h | h | h
  · left
    rw [h]
    apply Fin.ext
    norm_num [residue_val]
  · right; left
    rw [h]
    apply Fin.ext
    norm_num [residue_val]
  · right; right
    rw [h]
    apply Fin.ext
    norm_num [residue_val]

-- The named coloring separates the endpoints of a unit edge starting at the same boundary vertex.
example : sevenColor vertex ≠
    sevenColor (WithLp.toLp 2 ![(7 / 5 : ℝ), 2 / 15 * Real.sqrt 3]) := by
  apply sevenColor_ne_of_dist_eq_one
  apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)).1
  norm_num [vertex, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
