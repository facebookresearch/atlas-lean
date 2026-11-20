/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.CallPriceMonotoneConvex
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-! # Tests for `MathlibExt.Probability.Finance.CallPriceMonotoneConvex`

* The three-state example (`ψ = 1/3` each, `S = 80, 100, 120`): exact call prices
  `40/3`, `20/3`, `10/3` at strikes `90`, `100`, `110`.
* Antitone and convexity instances, including the strict convexity inequality
  `C(100) < (C(90) + C(110)) / 2`.
-/

@[expose] public section

open MathlibExt.Probability.Finance.CallPriceMonotoneConvex
open MathlibExt.Probability.Finance.OptionPayoffs

namespace MathlibExtTest.Probability.Finance.CallPriceMonotoneConvex

noncomputable def ψ : Fin 3 → ℝ := ![1/3, 1/3, 1/3]
noncomputable def S : Fin 3 → ℝ := ![80, 100, 120]

theorem hψ_test : ∀ ω, 0 ≤ ψ ω := by
  rw [Fin.forall_fin_succ]
  constructor
  · simp [ψ]
  · rw [Fin.forall_fin_succ]
    constructor
    · simp [ψ]
    · rw [Fin.forall_fin_succ]
      constructor
      · simp [ψ]
      · intro i
        exact Fin.elim0 i

theorem exact_90 : callPrice ψ S 90 = 40/3 := by
  simp only [callPrice, europeanCallPayoff, ψ, S, Fin.sum_univ_three]
  norm_num

theorem exact_100 : callPrice ψ S 100 = 20/3 := by
  simp only [callPrice, europeanCallPayoff, ψ, S, Fin.sum_univ_three]
  norm_num

theorem exact_110 : callPrice ψ S 110 = 10/3 := by
  simp only [callPrice, europeanCallPayoff, ψ, S, Fin.sum_univ_three]
  norm_num

theorem antitone_test : callPrice ψ S 110 ≤ callPrice ψ S 90 :=
  antitone_callPrice hψ_test (by norm_num : (90:ℝ) ≤ 110)

theorem convex_test :
    callPrice ψ S 100 ≤ (1/2 : ℝ) * callPrice ψ S 90 + (1/2 : ℝ) * callPrice ψ S 110 := by
  have hconv := convexOn_callPrice (ψ := ψ) (S := S) hψ_test
  have h := hconv.2 (Set.mem_univ (90 : ℝ)) (Set.mem_univ (110 : ℝ))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have harg : (1/2 : ℝ) * 90 + (1/2 : ℝ) * 110 = (100 : ℝ) := by norm_num
  rw [harg] at h
  exact h

theorem strict_test :
    callPrice ψ S 100 < (callPrice ψ S 90 + callPrice ψ S 110) / 2 := by
  rw [exact_90, exact_100, exact_110]
  norm_num

end MathlibExtTest.Probability.Finance.CallPriceMonotoneConvex
