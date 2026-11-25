/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ColoredPolygonDissectionComposition

open MetaMathlibExt

-- With one color for everything, the two compositions `(1, 2)` and `(2, 1)` of `3` give the
-- five dissections of a pentagon into two polygons: `4 * 5 = 10 * 2`.
example : coloredPolygonDissectionCount (fun _ => 1) 3 2 = 5 := by
  have h := succ_mul_coloredPolygonDissectionCount_eq (fun _ => 1) (n := 3) (k := 2)
    (by decide) (by decide)
  rw [coloredCompositionCount_one_three_two, show Nat.choose (3 + 2) 2 = 10 by decide] at h
  omega

-- With γ₁ = 2, γ₂ = 3 and γ₃ = 5, the 87 colored dissections of a hexagon by one diagonal give
-- `5 * 87 = 15 * 29`, and 29 = 2 * 5 + 3 * 3 + 5 * 2 counts the colored compositions
-- `(1, 3)`, `(2, 2)` and `(3, 1)` of `4`.
example : coloredCompositionCount (fun j => if j = 1 then 2 else if j = 2 then 3
    else if j = 3 then 5 else 0) 4 2 = 29 := by
  have h := succ_mul_coloredPolygonDissectionCount_eq (fun j => if j = 1 then 2
    else if j = 2 then 3 else if j = 3 then 5 else 0) (n := 4) (k := 2) (by decide) (by decide)
  rw [coloredPolygonDissectionCount_hexagon_two, show Nat.choose (4 + 2) 2 = 15 by decide] at h
  omega

-- For `k = 1` there is no diagonal: both counts are the colors of a single `(n+2)`-gon.
example (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    coloredPolygonDissectionCount γ n 1 = coloredCompositionCount γ n 1 := by
  have h := succ_mul_coloredPolygonDissectionCount_eq γ (k := 1) le_rfl hn
  rw [Nat.choose_one_right] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h

-- For `k = n` every polygon is a triangle. A hexagon has 14 triangulations, a Catalan number,
-- each weighted like the only composition `(1, 1, 1, 1)` of `4` into four parts.
example (γ : ℕ → ℕ) :
    coloredPolygonDissectionCount γ 4 4 = 14 * coloredCompositionCount γ 4 4 := by
  have h := succ_mul_coloredPolygonDissectionCount_eq γ (n := 4) (k := 4) (by decide) (by decide)
  rw [show Nat.choose (4 + 4) 4 = 70 by decide] at h
  omega
