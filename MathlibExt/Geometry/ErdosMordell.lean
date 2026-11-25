/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/898.lean` (the definition and statement of the inequality):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
-/
module

public import MathlibExt.Geometry.TwoD
import Mathlib.Analysis.Convex.Join
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# The Erdős–Mordell inequality

The sum of the distances from an interior point to the vertices of a triangle is at least twice
the sum of its distances to the three side lines. We prove a weighted bound at each vertex using
the area form, then sum the bounds.
-/

@[expose] public section

open Affine EuclideanGeometry
open scoped EuclideanGeometry EuclideanSpace

namespace MathlibExt.Geometry.ErdosProblem898Wanted

/-- **Statement of the Erdős–Mordell inequality.** Writing $XY$ for the distance between points
$X$ and $Y$, this is the assertion that for all affinely independent points $A$, $B$, $C$ of the
Euclidean plane, every point $P$ in the interior of the triangle $ABC$, and all points $M$, $N$,
$L$ on the lines $BC$, $AB$, $CA$ such that the lines $PM$, $PN$, $PL$ are perpendicular to $BC$,
$AB$, $CA$ respectively, we have $PA + PB + PC \ge 2(PM + PN + PL)$. -/
def conjecture : Prop :=
  ∀ (A B C P L M N : ℝ²) (_hABC : AffineIndependent ℝ ![A, B, C])
    (_hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)))
    (_hN : N ∈ line[ℝ, A, B])
    (_hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
    (_hM : M ∈ line[ℝ, B, C])
    (_hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction)
    (_hL : L ∈ line[ℝ, C, A])
    (_hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction),
    dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

local notation "ω" => Orientation.areaForm (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

/-- The parallelogram on a side and a point has area equal to base times height. -/
private lemma area_eq_base_mul_height {A B P F : ℝ²} (hF : F ∈ line[ℝ, A, B])
    (hPF : line[ℝ, P, F].direction ⟂ line[ℝ, A, B].direction) :
    |ω (P - A) (B - A)| = dist P F * dist B A := by
  have h := hPF.inner_eq (AffineSubspace.vsub_mem_direction
    (left_mem_affineSpan_pair ℝ P F) (right_mem_affineSpan_pair ℝ P F))
    (AffineSubspace.vsub_mem_direction (right_mem_affineSpan_pair ℝ A B)
      (left_mem_affineSpan_pair ℝ A B))
  have hzero : ω (F - A) (B - A) = 0 := by
    obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hF
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul, LinearMap.smul_apply,
      Orientation.areaForm_apply_self, smul_zero]
  rw [show P - A = (P - F) + (F - A) by abel, map_add, LinearMap.add_apply, hzero, add_zero]
  exact positiveOrientation.abs_areaForm_of_orthogonal h

/-- From any vertex, a point in the triangle is a nonnegative combination of the side vectors. -/
private lemma vertex_coordinates {A B C P : ℝ²} (hP : P ∈ convexHull ℝ {A, B, C}) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ P - A = s • (B - A) + t • (C - A) := by
  rw [← convexJoin_singleton_segment, convexJoin_singleton_left] at hP
  obtain ⟨Q, hQ, hPQ⟩ := Set.mem_iUnion₂.mp hP
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hQ
  obtain ⟨x, y, -, hy, hxy, rfl⟩ := hPQ
  refine ⟨y * s, y * t, mul_nonneg hy hs, mul_nonneg hy ht, ?_⟩
  rw [show x = 1 - y by linarith, show s = 1 - t by linarith]
  module

/-- Interchanging the lengths of the two side vectors preserves the opposite side length. -/
private lemma norm_swapped_sub {u v : ℝ²} (hu : 0 < ‖u‖) (hv : 0 < ‖v‖) :
    ‖(‖u‖ / ‖v‖) • v - (‖v‖ / ‖u‖) • u‖ = ‖u - v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_of_nonneg (div_nonneg hu.le hv.le), Real.norm_of_nonneg (div_nonneg hv.le hu.le),
    real_inner_smul_left, real_inner_smul_right, real_inner_comm v u]
  field_simp

/-- Inside the angle, the signed areas against the two sides contribute with the same sign
when paired with the difference of the rescaled side vectors. -/
private lemma weighted_area_le {u v w : ℝ²} {s t : ℝ} (hu : 0 < ‖u‖) (hv : 0 < ‖v‖)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hw : w = s • u + t • v) :
    ‖u‖ / ‖v‖ * |ω w v| + ‖v‖ / ‖u‖ * |ω w u| ≤ ‖w‖ * ‖u - v‖ := by
  let c := ‖u‖ / ‖v‖
  let b := ‖v‖ / ‖u‖
  have h₁ : ω w v = s * ω u v := by simp [hw]
  have h₂ : ω w u = -(t * ω u v) := by simp [hw, positiveOrientation.areaForm_swap v u]
  calc
    _ = |ω w (c • v - b • u)| := by
      rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h₁, h₂, abs_neg, abs_mul,
        abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      rw [show c * (s * ω u v) - b * -(t * ω u v) = (c * s + b * t) * ω u v by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ c * s + b * t by dsimp [c, b]; positivity)]
      dsimp [c, b]
      ring
    _ ≤ _ := (positiveOrientation.abs_areaForm_le _ _).trans_eq (by rw [norm_swapped_sub hu hv])

/-- The vertex distance times the opposite side bounds a weighted sum of the two heights. -/
private lemma vertex_bound {A B C P N L : ℝ²}
    (hAB : A ≠ B) (hCA : C ≠ A) (hP : P ∈ convexHull ℝ {A, B, C})
    (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
    (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    dist C A * dist P N + dist A B * dist P L ≤ dist P A * dist B C := by
  rw [Set.pair_comm C A] at hL hPL
  obtain ⟨s, t, hs, ht, hw⟩ := vertex_coordinates hP
  have hu : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have hv : 0 < ‖C - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hCA)
  have h := weighted_area_le hu hv hs ht hw
  rw [area_eq_base_mul_height hL hPL, area_eq_base_mul_height hN hPN,
    show B - A - (C - A) = B - C by abel] at h
  simp only [← dist_eq_norm] at h
  rw [dist_comm A B]
  have hBA := (dist_pos.mpr hAB.symm).ne'
  have hCA' := (dist_pos.mpr hCA).ne'
  calc
    _ = dist B A / dist C A * (dist P L * dist C A) +
        dist C A / dist B A * (dist P N * dist B A) := by field_simp; ring
    _ ≤ _ := h

private lemma twice_height_le {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 ≤ r) :
    2 * r ≤ x * r / y + y * r / x := by
  field_simp
  nlinarith only [mul_nonneg (sq_nonneg (x - y)) hr]

/--
**Erdős–Mordell inequality.** Let $A$, $B$, $C$ be affinely independent points of the Euclidean
plane and $P$ a point in the interior of the triangle $ABC$. Let $M$, $N$, $L$ be points on the
lines $BC$, $AB$, $CA$ such that $PM \perp BC$, $PN \perp AB$ and $PL \perp CA$. Then, writing
$XY$ for the distance between points $X$ and $Y$, we have $PA + PB + PC \ge 2(PM + PN + PL)$.

Source: Paul
Erdős, L. J. Mordell, and David F. Barrow, Problem 3740, American Mathematical Monthly 44
(1937), 252–254, https://doi.org/10.2307/2300713. Moved from
`OpenConjectures/Geometry/ErdosProblem898`.
-/
theorem conjecture_holds : conjecture := by
  intro A B C P L M N hABC hP hN hPN hM hPM hL hPL
  have hAB : A ≠ B := hABC.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hBC : B ≠ C := hABC.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hCA : C ≠ A := hABC.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
  have h := interior_subset hP
  have hA := (div_le_iff₀ (dist_pos.mpr hBC)).2 (vertex_bound hAB hCA h hN hPN hL hPL)
  have hB := (div_le_iff₀ (dist_pos.mpr hCA)).2
    (vertex_bound hBC hAB (by rwa [Set.pair_comm C A, Set.insert_comm B A]) hM hPM hN hPN)
  have hC := (div_le_iff₀ (dist_pos.mpr hAB)).2
    (vertex_bound hCA hBC (by rwa [Set.insert_comm C A, Set.pair_comm C B]) hL hPL hM hPM)
  simp only [add_div] at hA hB hC
  linarith only [hA, hB, hC,
    twice_height_le (dist_pos.mpr hAB) (dist_pos.mpr hCA) (dist_nonneg (x := P) (y := M)),
    twice_height_le (dist_pos.mpr hBC) (dist_pos.mpr hCA) (dist_nonneg (x := P) (y := N)),
    twice_height_le (dist_pos.mpr hAB) (dist_pos.mpr hBC) (dist_nonneg (x := P) (y := L))]

end MathlibExt.Geometry.ErdosProblem898Wanted
