/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorApproximantPrimeCounting

/-! # A concrete weight for the exponential divisor-count estimate -/

namespace MetaMathlibExt

open Asymptotics Filter Finset

-- The reciprocal of the squared sine saturates the hypothesis at every nondivisor.
example :
    (fun n : ℕ => ∑ k ∈ Icc 1 n,
      Real.exp (-(n * k * (Real.sin (n * Real.pi / k) ^ 2)⁻¹ * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1) := by
  apply divisorCountApprox_sub_isBigO (fun k n => (Real.sin (n * Real.pi / k) ^ 2)⁻¹)
  intro k n hk _ hnd
  have hs : Real.sin (n * Real.pi / k) ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hzero
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have heq : (n : ℝ) = k * z := by
      apply mul_right_cancel₀ Real.pi_ne_zero
      simpa only [mul_assoc, mul_comm, mul_left_comm] using ((eq_div_iff hk').mp hz).symm
    exact hnd (Int.natCast_dvd_natCast.mp ⟨z, by exact_mod_cast heq⟩)
  simp [hs]

end MetaMathlibExt
