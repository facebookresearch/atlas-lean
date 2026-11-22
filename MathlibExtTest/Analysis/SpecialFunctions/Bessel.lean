/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.SpecialFunctions.Bessel

@[expose] public section

namespace MathlibExtTest.Analysis.SpecialFunctions.Bessel

open MetaMathlibExt

-- Analysis 380: Bessel Function of the First Kind

theorem besselJ_zero_zero :
    besselJ 0 0 = 1 := by
  unfold besselJ
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro k hk
    have h_exp :
        (((2 * k : ℕ) : ℂ) + ((0 : ℝ) : ℂ)) ≠ 0 := by
      simp only [Complex.ofReal_zero, add_zero, ne_eq, Nat.cast_eq_zero]
      omega
    simp
    omega
  · simp [Complex.Gamma_one]

end MathlibExtTest.Analysis.SpecialFunctions.Bessel

end
