/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.FundedFTAP
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.FundedFTAP` -/

open MathlibExt.Probability.Finance.FundedFTAP

namespace MathlibExtTest.FundedFTAP

/-- Test payoffs: one asset paying `3` in state `0` and `1` in state `1`. -/
def testX : Unit → Fin 2 → ℝ := fun _ ω => if ω = 0 then 3 else 1

/-- Test price: the asset costs `1`. -/
def testP : Unit → ℝ := fun _ => 1

/-- With `R = 2` the funded gains are `(1, -1)`, the market is arbitrage-free,
and the risk-neutral probability is `(1/2, 1/2)`. -/
example : ∃ q : Fin 2 → ℝ, (∀ ω, 0 < q ω) ∧ (∑ ω, q ω = 1) ∧
    (∀ a : Unit, ∑ ω, q ω * testX a ω = 2 * testP a) ∧ q 0 = 1 / 2 ∧ q 1 = 1 / 2 := by
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hX0 : testX () 0 = 3 := by simp [testX]
  have hX1 : testX () 1 = 1 := by simp [testX, hne10]
  have hP : testP () = 1 := rfl
  have hNA : ¬ ∃ h : Unit → ℝ,
      (∀ ω : Fin 2, 0 ≤ ∑ a : Unit, h a * (testX a ω - 2 * testP a)) ∧
      (∃ ω : Fin 2, 0 < ∑ a : Unit, h a * (testX a ω - 2 * testP a)) := by
    rintro ⟨h, hnonneg, ω, hpos⟩
    have h0 := hnonneg 0
    have h1 := hnonneg 1
    simp only [Fintype.univ_unit, Finset.sum_singleton] at h0 h1 hpos
    rw [hX0, hP] at h0
    rw [hX1, hP] at h1
    norm_num at h0 h1
    have hh : h () = 0 := by linarith
    rw [hh, zero_mul] at hpos
    simp at hpos
  obtain ⟨q, hqpos, hqsum, hE⟩ := (funded_ftap testX testP 2).mp hNA
  have hE0 := hE ()
  have hqsum2 := hqsum
  rw [hP] at hE0
  rw [Fin.sum_univ_two] at hE0 hqsum2
  rw [hX0, hX1] at hE0
  have hq0 : q 0 = 1 / 2 := by linarith
  have hq1 : q 1 = 1 / 2 := by linarith
  exact ⟨q, hqpos, hqsum, hE, hq0, hq1⟩

end MathlibExtTest.FundedFTAP
