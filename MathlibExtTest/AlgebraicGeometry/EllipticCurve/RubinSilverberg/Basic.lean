/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.Basic

import Mathlib.Algebra.Field.ZMod

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

-- Boundary: `IsKleinDatum` also requires `V(u₀) ≠ 0`. For the singular curve `a = -3`, `b = 2`
-- (`4a³ + 27b² = 0`) the Klein relation holds at the vertex `u₀ = 0`, where `V(0) = 0`, but
-- `IsKleinDatum` does not.
example : kleinH (0 : ℚ) ^ 3 * (4 * (-3) ^ 3 + 27 * 2 ^ 2) + 6912 * (-3) ^ 3 * kleinV (0 : ℚ) ^ 5
      = 0 ∧ ¬ IsKleinDatum (-3 : ℚ) 2 0 := by
  norm_num [IsKleinDatum, kleinH, kleinV]

-- Klein data with `a b ≠ 0`: in characteristic zero, the coefficients of `kleinCurve u` at any `u`
-- with `V(u) ≠ 0`; at `u = 1` this is `kleinCurve 1 : y² = x³ - 31/3 x - 2501/108`.
example {K : Type*} [Field K] [CharZero K] (u : K) (hV : kleinV u ≠ 0) :
    IsKleinDatum (-kleinH u / 48) (kleinT u / 864) u := by
  refine ⟨?_, hV⟩
  have hs := kleinT_sq_sub_kleinH_cube u
  field_simp
  linear_combination 2985984 * kleinH u ^ 3 * hs

example : IsKleinDatum (-31 / 3 : ℚ) (-2501 / 108) 1 := by
  norm_num [IsKleinDatum, kleinH, kleinV]

-- When `6` is invertible, `kleinCurve u` has discriminant `-V(u)⁵` and `c₄ = H(u)`, so for
-- `V(u) ≠ 0` it is elliptic with `j`-invariant `-H(u)³ / V(u)⁵`.
private theorem kleinCurve_Δ_c₄ {K : Type*} [Field K] (h6 : (6 : K) ≠ 0) (u : K) :
    (kleinCurve u).Δ = -kleinV u ^ 5 ∧ (kleinCurve u).c₄ = kleinH u := by
  have h2 : (2 : K) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
  have h3 : (3 : K) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
  have h48 : (48 : K) ≠ 0 := by
    rw [show (48 : K) = 2 ^ 4 * 3 by norm_num]; exact mul_ne_zero (pow_ne_zero _ h2) h3
  have h864 : (864 : K) ≠ 0 := by
    rw [show (864 : K) = 2 ^ 5 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hs := kleinT_sq_sub_kleinH_cube u
  constructor
  · simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, kleinCurve]
    field_simp
    linear_combination (-47775744 : K) * hs
  · simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, kleinCurve]
    field_simp
    ring

example {K : Type*} [Field K] (h6 : (6 : K) ≠ 0) (u : K) (hV : kleinV u ≠ 0) :
    ∃ _ : (kleinCurve u).IsElliptic, (kleinCurve u).j = -kleinH u ^ 3 / kleinV u ^ 5 := by
  obtain ⟨hΔ, hc₄⟩ := kleinCurve_Δ_c₄ h6 u
  have : (kleinCurve u).IsElliptic :=
    ⟨by rw [hΔ]; exact (neg_ne_zero.mpr (pow_ne_zero 5 hV)).isUnit⟩
  refine ⟨this, ?_⟩
  rw [WeierstrassCurve.j_eq, hΔ, hc₄]
  ring

-- Boundary: when `6 = 0` in `K` (characteristic `2` or `3`), `48 = 864 = 0`, so `kleinCurve u` is
-- the singular cubic `y² = x³`, as over `ZMod 2`.
private theorem kleinCurve_of_six_eq_zero {K : Type*} [Field K] (h6 : (6 : K) = 0) (u : K) :
    kleinCurve u = ⟨0, 0, 0, 0, 0⟩ := by
  have h48 : (48 : K) = 0 := by rw [show (48 : K) = 6 * 8 by norm_num, h6, zero_mul]
  have h864 : (864 : K) = 0 := by rw [show (864 : K) = 6 * 144 by norm_num, h6, zero_mul]
  simp [kleinCurve, h48, h864]

example (u : ZMod 2) : kleinCurve u = ⟨0, 0, 0, 0, 0⟩ := kleinCurve_of_six_eq_zero (by decide) u
