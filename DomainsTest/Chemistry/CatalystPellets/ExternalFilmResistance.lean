/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.CatalystPellets.ExternalFilmResistance

open MathlibExt.Chemistry.CatalystPellets.ExternalFilmResistance

-- With zero intrinsic rate there is no concentration drop and no observed rate.
example (cb : ℝ) (hcb : 0 ≤ cb) :
    (∀ cs : ℝ, 0 = 3 * (cb - cs) ↔ cs = cb) ∧
    ((1 / 2 : ℝ) * 0 * 3 / ((1 / 2 : ℝ) * 0 + 3)) * cb = 0 := by
  obtain ⟨hsurface, _, hzero, _, _, _⟩ :=
    external_film_resistance 0 cb (1 / 2) 3 1 1 (by norm_num) hcb
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · intro cs
    simpa using hsurface cs
  · simpa only [div_self one_ne_zero, one_mul] using hzero rfl

-- Internal η = 1/2, k = 2 and Kf = 3. At cb = 4 the surface solution and rate are both 3.
example :
    ((1 / 2 : ℝ) * 2 * 3 / ((1 / 2 : ℝ) * 2 + 3)) = 3 / 4 ∧
    ((1 / 2 : ℝ) * 2 * 3 / ((1 / 2 : ℝ) * 2 + 3)) / 2 = 3 / 8 := by
  obtain ⟨hsurface, hrate, _, _, _, _⟩ :=
    external_film_resistance 2 4 (1 / 2) 3 1 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbalance := (hsurface 3).mpr (by norm_num)
  have hcoefficient : ((1 / 2 : ℝ) * 2 * 3 / ((1 / 2 : ℝ) * 2 + 3)) = 3 / 4 := by
    apply (eq_div_iff (by norm_num : (4 : ℝ) ≠ 0)).mpr
    simpa only [div_self one_ne_zero, one_mul, show (1 / 2 : ℝ) * 2 * 3 = 3 by norm_num]
      using (hrate 3 hbalance).symm
  refine ⟨hcoefficient, ?_⟩
  rw [hcoefficient]
  norm_num
