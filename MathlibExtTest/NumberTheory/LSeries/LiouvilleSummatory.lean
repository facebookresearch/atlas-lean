/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.LiouvilleSummatory
import MathlibExt.NumberTheory.LSeries.RiemannXi

/-!
# Tests for the summatory Liouville function and zeros of `ζ`
-/

@[expose] public section

open MetaMathlibExt.LiouvilleSummatory

namespace LiouvilleSummatoryTest

/-- `ζ(1/2) ≠ 0`. -/
example : riemannZeta (1 / 2 : ℝ) ≠ 0 :=
  riemannZeta_ofReal_ne_zero_of_pos_of_lt_one (by norm_num) (by norm_num)

/-- The real interval `(0, 1)` contains no nontrivial zero. -/
example {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : (σ : ℂ) ∉ riemannZetaNontrivialZeros :=
  fun h => riemannZeta_ofReal_ne_zero_of_pos_of_lt_one h0 h1 h.1

/-- Pólya's conjecture (`∑_{n ≤ N} λ(n) ≤ 0` eventually) would imply that `ζ` has no zeros with
`Re s > 1/2`. -/
example (h : ∀ᶠ N : ℕ in Filter.atTop,
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n ≤ 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_liouville_sum_constant_sign (.inr h) hs

end LiouvilleSummatoryTest
