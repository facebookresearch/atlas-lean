/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Basic

@[expose] public section

open RubinSilverberg

-- Consumers with the original binders.
private theorem exactSource_rsBeta_sub_mul_rsGamma {K : Type*} [Field K] (u : K) (_hu : u ≠ 0)
    (_hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0) :
    rsBeta u - u * rsGamma u =
      -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) :=
  rsBeta_sub_mul_rsGamma u

private theorem exactSource_kleinH_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K}
    (h : RubinSilverberg.IsKleinDatum a b u₀) (ha : a ≠ 0) : RubinSilverberg.kleinH u₀ ≠ 0 :=
  h.kleinH_ne_zero ha

private theorem exactSource_kleinT_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K}
    (h : RubinSilverberg.IsKleinDatum a b u₀) (hb : b ≠ 0) : RubinSilverberg.kleinT u₀ ≠ 0 :=
  h.kleinT_ne_zero hb

-- Klein's forms at `u = 0` and `u = 1`, and the syzygy `T² - H³ = 1728 V⁵` there.
example : kleinV (0 : ℚ) = 0 ∧ kleinH (0 : ℚ) = 1 ∧ kleinT (0 : ℚ) = 1 := by
  norm_num [kleinV, kleinH, kleinT]

example : kleinV (1 : ℚ) = 11 ∧ kleinH (1 : ℚ) = 496 ∧ kleinT (1 : ℚ) = -20008 := by
  norm_num [kleinV, kleinH, kleinT]

example : (-20008 : ℚ) ^ 2 - 496 ^ 3 = 1728 * 11 ^ 5 := by norm_num

example (u : ℚ) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 :=
  kleinT_sq_sub_kleinH_cube u

-- Boundary: `IsKleinDatum` requires `V(u₀) ≠ 0`; the Klein relation alone holds at the
-- vertex `u₀ = 0` for the curve with `a = 0`, where `kleinH` does not vanish but `a` does.
example : ¬ IsKleinDatum (0 : ℚ) 1 0 := by
  simp [IsKleinDatum, kleinV]
