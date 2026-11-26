/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicProductRamanujanSums

/-! # Tests for the zeta-twisted cyclotomic product -/

open Filter MetaMathlibExt Topology

-- The common limit must be 1 at z = 0, since every partial product on the left is 1.
example {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.Icc 1 N,
      Complex.exp (-(riemannZeta (s : ℂ) / (((i : ℝ) ^ s : ℝ) : ℂ)) *
        ∑ ζ ∈ primitiveRoots i ℂ, Complex.log (1 - (0 : ℂ) * ζ))) atTop (𝓝 1) := by
  obtain ⟨L, hleft, hright⟩ :=
    exists_tendsto_prod_one_sub_pow_and_cyclotomicHat_zeta (z := 0) (s := s)
      (hz := by simp) (hs := hs)
  have hzero (N : ℕ) : ∏ i ∈ Finset.Icc 1 N,
      Complex.exp (-(((i : ℝ) ^ s : ℝ) : ℂ)⁻¹ * Complex.log (1 - (0 : ℂ) ^ i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hi0 : i ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hi).1
    simp [hi0]
  have hL : L = 1 := tendsto_nhds_unique (by simpa only [hzero] using hleft) tendsto_const_nhds
  simpa only [hL] using hright
