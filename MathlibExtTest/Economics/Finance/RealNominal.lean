/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Finance.RealNominal
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Finance.RealNominal`

Real flows `(-100, 60, 60)` at real rate `1/10` and inflation `1/20` have the same present value
`500/121` in real and nominal terms; discounting nominal flows at the real rate gives a different
value. -/

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.RealNominal

namespace MathlibExtTest.Economics.Finance.RealNominal

noncomputable def exampleCash : ℕ → ℝ :=
  fun t => if t = 0 then -100 else if t ≤ 2 then 60 else 0

theorem example_real_pv :
    presentValue (discountFactor (1 / 10)) (Finset.range 3) exampleCash = 500 / 121 := by
  simp [presentValue, discountFactor, exampleCash, Finset.sum_range_succ]
  norm_num

theorem example_nominal_pv :
    presentValue (discountFactor ((1 + 1 / 10) * (1 + 1 / 20) - 1)) (Finset.range 3)
        (fun t => (1 + 1 / 20) ^ t * exampleCash t) = 500 / 121 := by
  have h := presentValue_nominal_eq_real_const (r := (1 / 10 : ℝ)) (π := (1 / 20 : ℝ))
    (by norm_num) (Finset.range 3) exampleCash
  rw [h]
  exact example_real_pv

theorem example_mismatch_eq :
    presentValue (discountFactor (1 / 10)) (Finset.range 3)
        (fun t => (1 + 1 / 20) ^ t * exampleCash t) = 1445 / 121 := by
  simp [presentValue, discountFactor, exampleCash, Finset.sum_range_succ]
  norm_num

theorem example_mismatch_ne :
    presentValue (discountFactor (1 / 10)) (Finset.range 3)
        (fun t => (1 + 1 / 20) ^ t * exampleCash t) ≠ 500 / 121 := by
  rw [example_mismatch_eq]
  norm_num

end MathlibExtTest.Economics.Finance.RealNominal
