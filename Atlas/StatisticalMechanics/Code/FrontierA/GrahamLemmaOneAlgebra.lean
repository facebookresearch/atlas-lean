/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib









namespace StatMech.FrontierA







theorem grahamSimonComparison_algebra
    (a b c d e x y v : Real)
    (hv : 0 < v) (hb : 0 <= b) (hx : 0 <= x) (hy : 0 <= y)
    (hvar : v = 1 - b ^ 2)
    (hghs : 2 * b * x * y <= v * (d * x + a * y - (e - c * b)))
    (hbridgeA : 0 <= a * v - b * x)
    (hbridgeD : 0 <= d * v - b * y) :
    v * (c - a * d) <= c - e * b := by
  have hxy : 0 <= x * y := mul_nonneg hx hy
  have hbxy : 0 <= b ^ 2 * (x * y) := mul_nonneg (sq_nonneg b) hxy
  have hbridges : 0 <= (a * v - b * x) * (d * v - b * y) :=
    mul_nonneg hbridgeA hbridgeD
  have hscaled :
      b * v * (e - c * b) <= a * d * v ^ 2 := by
    have hbghs := mul_le_mul_of_nonneg_left hghs hb
    nlinarith
  have hcancel : b * (e - c * b) <= a * d * v := by
    by_contra h
    have hlt : a * d * v < b * (e - c * b) := lt_of_not_ge h
    have := mul_lt_mul_of_pos_right hlt hv
    nlinarith
  rw [hvar] at hcancel ⊢
  nlinarith

end StatMech.FrontierA
