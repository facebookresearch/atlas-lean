/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowN
import Mathlib.Tactic.NormNum

open scoped BigOperators
open MathlibExt.Analysis.Complex.ZerosOfSumZDivNPowNWanted

/-- The series has constant term one. -/
example : F 0 = 1 := by simp [F]

/-- The quantitative bound forces zero total multiplicity in the disk of radius `1/8`. -/
example : ∃ s : Finset ℂ,
    (∀ z : ℂ, z ∈ s ↔ ‖z‖ < (1 / 8 : ℝ) ∧ F z = 0) ∧
    (∑ z ∈ s, analyticOrderNatAt F z) = 0 := by
  obtain ⟨s, hs, hCount⟩ := exists_finset_zeros_sum_analyticOrderNatAt_le (1 / 8) (by norm_num)
  refine ⟨s, hs, ?_⟩
  have hReal : ((∑ z ∈ s, analyticOrderNatAt F z) : ℝ) < 1 :=
    hCount.trans_lt (by norm_num)
  have hNat : (∑ z ∈ s, analyticOrderNatAt F z) < 1 := by exact_mod_cast hReal
  exact Nat.lt_one_iff.mp hNat
