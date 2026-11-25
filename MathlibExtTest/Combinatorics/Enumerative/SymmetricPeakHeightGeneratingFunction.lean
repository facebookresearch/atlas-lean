/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction` -/

namespace MathlibExtTest.SymmetricPeakHeightGeneratingFunction

open MetaMathlibExt PowerSeries

/-- The total symmetric peak height over the compositions of `n`, as an integer. -/
private def hsp (n : ℕ) : ℤ :=
  ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)

/-- The coefficient of `xⁿ` in the identity, where a term `hsp (n - k)` with `n < k` is absent:
`hsp n - 4 hsp (n - 1) + 4 hsp (n - 2) - hsp (n - 3) + 4 hsp (n - 4) - 4 hsp (n - 5)` is `1`
for `n = 4` and `0` otherwise. -/
private theorem coeff_identity (n : ℕ) :
    hsp n - 4 * (if 1 ≤ n then hsp (n - 1) else 0) + 4 * (if 2 ≤ n then hsp (n - 2) else 0) -
        (if 3 ≤ n then hsp (n - 3) else 0) + 4 * (if 4 ≤ n then hsp (n - 4) else 0) -
        4 * (if 5 ≤ n then hsp (n - 5) else 0) = if n = 4 then 1 else 0 := by
  have h := congrArg (coeff n) symmetricPeakHeightSum_compositions_genFun
  have hP : ∀ H : ℤ⟦X⟧, H * ((1 - 2 * X) ^ 2 * (1 - X ^ 3)) = H - C 4 * (X ^ 1 * H) +
      C 4 * (X ^ 2 * H) - X ^ 3 * H + C 4 * (X ^ 4 * H) - C 4 * (X ^ 5 * H) := by
    intro H
    simp only [map_ofNat, pow_one]
    ring
  rw [hP] at h
  simpa only [hsp, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    using h

-- Comparing the coefficients of `xⁿ⁺⁵` gives the order-five recurrence satisfied by `hsp`.
example (n : ℕ) :
    hsp (n + 5) =
      4 * hsp (n + 4) - 4 * hsp (n + 3) + hsp (n + 2) - 4 * hsp (n + 1) + 4 * hsp n := by
  have h := coeff_identity (n + 5)
  simp only [show 1 ≤ n + 5 by omega, show 2 ≤ n + 5 by omega, show 3 ≤ n + 5 by omega,
    show 4 ≤ n + 5 by omega, show 5 ≤ n + 5 by omega, show n + 5 - 1 = n + 4 by omega,
    show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega,
    show n + 5 - 4 = n + 1 by omega, show n + 5 - 5 = n by omega,
    show ¬n + 5 = 4 by omega, ↓reduceIte] at h
  linarith

-- The first values. No composition of `n ≤ 3` has a symmetric peak and `1 2 1` is the only one
-- for `n = 4`; for `n = 5` the compositions `1 3 1`, `1 2 1 1` and `1 1 2 1` give `2 + 1 + 1`,
-- as in the example after Corollary 3 of arXiv:2408.09166v1.
example : hsp 0 = 0 ∧ hsp 1 = 0 ∧ hsp 2 = 0 ∧ hsp 3 = 0 ∧ hsp 4 = 1 ∧ hsp 5 = 4 ∧
    hsp 6 = 12 ∧ hsp 7 = 33 := by
  have h0 := coeff_identity 0
  have h1 := coeff_identity 1
  have h2 := coeff_identity 2
  have h3 := coeff_identity 3
  have h4 := coeff_identity 4
  have h5 := coeff_identity 5
  have h6 := coeff_identity 6
  have h7 := coeff_identity 7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  omega

end MathlibExtTest.SymmetricPeakHeightGeneratingFunction
