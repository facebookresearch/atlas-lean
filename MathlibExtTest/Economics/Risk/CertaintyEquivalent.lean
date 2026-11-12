/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Risk.CertaintyEquivalent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Risk.CertaintyEquivalent`

A fifty-fifty lottery over prizes `0` and `4` under `√` has certainty equivalent `1` (risk premium
`1`), and no other. -/

open Convexity
open MathlibExt.Economics.ExpectedUtility
open MathlibExt.Economics.Risk

namespace MathlibExtTest.Economics.Risk.CertaintyEquivalent

/-- The 50-50 lottery on `Fin 2`: weights `1 / 2, 1 / 2`. -/
noncomputable def exLottery : StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple (0 : Fin 2) (1 : Fin 2)
    (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)

theorem exLottery_weights_zero : exLottery.weights 0 = 1 / 2 := by
  simp only [exLottery, StdSimplex.weights_duple]
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero]

theorem exLottery_weights_one : exLottery.weights 1 = 1 / 2 := by
  simp only [exLottery, StdSimplex.weights_duple]
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]

/-- The expected square-root utility of the 50-50 lottery over prizes `0, 4` is `1`. -/
theorem ex_expected : expectedUtility (Real.sqrt ∘ ![0, 4]) exLottery = 1 := by
  have hw0 : exLottery.weights 0 = 1 / 2 := exLottery_weights_zero
  have hw1 : exLottery.weights 1 = 1 / 2 := exLottery_weights_one
  have hz0 : (![0, 4] : Fin 2 → ℝ) 0 = 0 := by simp
  have hz1 : (![0, 4] : Fin 2 → ℝ) 1 = 4 := by simp
  have hsqrt4 : Real.sqrt 4 = 2 := by
    have h : (2:ℝ) ^ 2 = 4 := by norm_num
    rw [← h]
    exact Real.sqrt_sq (by norm_num)
  simp only [expectedUtility, Function.comp_apply, Fin.sum_univ_two]
  rw [hw0, hw1, hz0, hz1, Real.sqrt_zero, hsqrt4]
  norm_num

/-- (a) `1` is a certainty equivalent of the 50-50 lottery over `0, 4` for `Real.sqrt`. -/
theorem ex_certaintyEquivalent :
    IsCertaintyEquivalent (Set.Icc 0 4) Real.sqrt ![0, 4] exLottery 1 := by
  refine ⟨Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [ex_expected]
  exact Real.sqrt_one

/-- (b) Any certainty equivalent of that lottery for `Real.sqrt` equals `1`
(the mean prize is `2`, so the risk premium is `1`). -/
theorem ex_unique (c : ℝ)
    (hc : IsCertaintyEquivalent (Set.Icc 0 4) Real.sqrt ![0, 4] exLottery c) : c = 1 := by
  have hmono : StrictMonoOn Real.sqrt (Set.Icc 0 4) :=
    Real.strictMonoOn_sqrt.mono Set.Icc_subset_Ici_self
  exact IsCertaintyEquivalent.unique hmono hc ex_certaintyEquivalent

end MathlibExtTest.Economics.Risk.CertaintyEquivalent
