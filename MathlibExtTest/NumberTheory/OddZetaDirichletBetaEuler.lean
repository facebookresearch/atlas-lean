/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.NumberTheory.OddZetaDirichletBetaEuler

/-! # Tests for `MathlibExt.NumberTheory.OddZetaDirichletBetaEuler` -/

namespace MathlibExtTest.NumberTheory.OddZetaDirichletBetaEuler

open scoped Topology

/-- At `k = 2`, the odd-denominator series is `π² / 8`: the factor
`(1 - 1 / 2 ^ 2) = 3 / 4` times `ζ(2) = π² / 6`. -/
example : ∑' n : ℕ, 1 / (2 * (n : ℂ) + 1) ^ 2 = (Real.pi : ℂ) ^ 2 / 8 := by
  have h := (MetaMathlibExt.hasSum_one_div_odd_pow 2 (by norm_num)).tsum_eq
  have hz : (1 - 1 / (2 : ℂ) ^ 2) * riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 8 := by
    rw [riemannZeta_two]
    ring
  simpa only [Nat.cast_ofNat] using h.trans hz

end MathlibExtTest.NumberTheory.OddZetaDirichletBetaEuler
