/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.EllipticBilliard602

namespace MathlibExtTest.Geometry.EllipticBilliard602

open MathlibExt.Geometry.EllipticBilliard602Wanted

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private def point (x y : ℝ) : Plane := !₂[x, y]

private theorem norm_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem horizontal_line {a b : ℝ} (hab : a ≠ b) (x : Plane) :
    (∃ t : ℝ, x = point a 3 + t • (point b 3 - point a 3)) ↔ x 1 = 3 := by
  constructor
  · rintro ⟨t, ht⟩
    have hy := congrArg (fun p : Plane => p 1) ht
    change x 1 = 3 + t * (3 - 3) at hy
    simpa using hy
  · intro hx
    refine ⟨(x 0 - a) / (b - a), PiLp.ext fun i => ?_⟩
    fin_cases i
    · change x 0 = a + (x 0 - a) / (b - a) * (b - a)
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm)]
      ring
    · change x 1 = 3 + (x 0 - a) / (b - a) * (3 - 3)
      simp [hx]

private noncomputable def circularCase :=
  Classical.indefiniteDescription _ <|
    conjecture_holds 2 (0 : Plane) 0 0 10 6 (by simp) (by norm_num) (by norm_num) (by norm_num)

-- The sequence alternates between (4, 3) and (-4, 3) on the circle of radius 5.
-- Both sidelines touch the caustic of radius 3 at (0, 3).
example : circularCase.val = 81 := by
  let xcoord := fun i : ℕ => if i % 2 = 0 then (4 : ℝ) else -4
  let P := fun i : ℕ => point (xcoord i) 3
  let q := point 0 3
  have hcoord (i : Fin 2) : xcoord i ≠ xcoord (i.val + 1) := by
    fin_cases i <;> norm_num [xcoord]
  have hside (i : Fin 2) (x : Plane) :
      (∃ t : ℝ, x = P i.val + t • (P (i.val + 1) - P i.val)) ↔ x 1 = 3 :=
    horizontal_line (hcoord i) x
  have hqnorm : ‖q‖ = 3 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [norm_sq]
    change (0 : ℝ) ^ 2 + 3 ^ 2 = 3 ^ 2
    norm_num
  have htangent (i : Fin 2) :
      ∃! x : Plane,
        (∃ t : ℝ, x = P i.val + t • (P (i.val + 1) - P i.val)) ∧
          dist x 0 + dist x 0 = 6 := by
    refine ⟨q, ⟨(hside i q).2 rfl, by norm_num [hqnorm]⟩, ?_⟩
    rintro x ⟨hx, hsum⟩
    have hy := (hside i x).1 hx
    have hn : ‖x‖ = 3 := by simp only [dist_zero_right] at hsum; linarith
    have hs := norm_sq x
    rw [hy, hn] at hs
    have hz : x 0 ^ 2 = 0 := by linarith
    exact PiLp.ext fun j => by
      fin_cases j
      · exact sq_eq_zero_iff.mp hz
      · exact hy
  have hclosest (i : Fin 2) :
      (∃ t : ℝ, q = P i.val + t • (P (i.val + 1) - P i.val)) ∧
        ∀ x : Plane, (∃ t : ℝ, x = P i.val + t • (P (i.val + 1) - P i.val)) →
          dist 0 q ≤ dist 0 x := by
    refine ⟨(hside i q).2 rfl, fun x hx => ?_⟩
    rw [dist_zero_left, dist_zero_left, hqnorm]
    apply le_of_sq_le_sq _ (norm_nonneg x)
    rw [norm_sq, (hside i x).1 hx]
    linarith [sq_nonneg (x 0)]
  have hval := circularCase.property P (fun _ => q) (fun _ => q) (by
    intro i
    have hnorm : ‖P i‖ = 5 := by
      refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
      rw [norm_sq]
      change xcoord i ^ 2 + 3 ^ 2 = 5 ^ 2
      by_cases hi : i % 2 = 0 <;> norm_num [xcoord, hi]
    norm_num [hnorm]) (by
      intro i
      simp [P, xcoord]) (by
      intro i h
      exact hcoord i (congrArg (fun p : Plane => p 0) h)) htangent hclosest hclosest
  calc
    circularCase.val = (∏ _i : Fin 2, dist 0 q) * (∏ _i : Fin 2, dist 0 q) := hval.symm
    _ = 81 := by norm_num [hqnorm]

end MathlibExtTest.Geometry.EllipticBilliard602
