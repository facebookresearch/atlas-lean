/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.SolowGrowthAccounting

import Mathlib.Tactic

/-!
# Tests for growth accounting

Concrete instance `F (K, L) = K + L`, `F' = fst + snd`, `A = 1`, `K t = t`,
`L t = 2 * t`, at `t = 1`: `Y = 3`, growth `= 1`, elasticities `1/3` and
`2/3`, competitive shares sum to 1.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.SolowGrowthAccounting

open MathlibExt.Economics.Macro.SolowGrowthAccounting

-- Test section: concrete instance `F p = p.1 + p.2`, `F' = fst + snd`,
-- `A ≡ 1`, `K t = t`, `L t = 2 * t` at `t = 1`, proved via the pinned
-- theorems plus computation.
noncomputable def testF : ℝ × ℝ → ℝ := fun p => p.1 + p.2

noncomputable def testF' : ℝ × ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ

noncomputable def testA : ℝ → ℝ := fun _ => 1

noncomputable def testK : ℝ → ℝ := fun t => t

noncomputable def testL : ℝ → ℝ := fun t => 2 * t

noncomputable def testY : ℝ → ℝ := fun s => testA s * testF (testK s, testL s)

theorem testF_12 : testF (1, 2) = 3 := by norm_num [testF]

theorem testFderiv_10 : testF' (1, 0) = 1 := by
  simp [testF', add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem testFderiv_01 : testF' (0, 1) = 1 := by
  simp [testF', add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem testA_1 : testA 1 = 1 := rfl

theorem testK_1 : testK 1 = 1 := rfl

theorem testL_1 : testL 1 = 2 := by simp [testL]

theorem testY_1 : testY 1 = 3 := by
  show testA 1 * testF (testK 1, testL 1) = 3
  rw [testA_1, testK_1, testL_1, testF_12, one_mul]

theorem testcap : capitalElasticity testF testF' 1 2 = 1 / 3 := by
  unfold capitalElasticity
  rw [testFderiv_10, testF_12]
  norm_num

theorem testlab : labourElasticity testF testF' 1 2 = 2 / 3 := by
  unfold labourElasticity
  rw [testFderiv_01, testF_12]
  norm_num

theorem testA_hasDeriv : HasDerivAt testA 0 1 := by
  unfold testA
  exact hasDerivAt_const (1 : ℝ) (1 : ℝ)

theorem testK_hasDeriv : HasDerivAt testK 1 1 := by
  unfold testK
  exact hasDerivAt_id (1 : ℝ)

theorem testL_hasDeriv : HasDerivAt testL 2 1 := by
  have h := (hasDerivAt_id (1 : ℝ)).const_mul (2 : ℝ)
  show HasDerivAt (fun t : ℝ => 2 * t) 2 1
  simpa using h

theorem testF_hasFDeriv : HasFDerivAt testF testF' (testK 1, testL 1) :=
  hasFDerivAt_fst.add hasFDerivAt_snd

theorem testderivA : deriv testA 1 = 0 := testA_hasDeriv.deriv

theorem testderivK : deriv testK 1 = 1 := testK_hasDeriv.deriv

theorem testderivL : deriv testL 1 = 2 := testL_hasDeriv.deriv

example : deriv testY 1 / testY 1 = 1 := by
  have hY : ∀ s, testY s = testA s * testF (testK s, testL s) := fun s => rfl
  have hA0 : testA 1 ≠ 0 := by rw [testA_1]; exact one_ne_zero
  have hK0 : testK 1 ≠ 0 := by rw [testK_1]; exact one_ne_zero
  have hL0 : testL 1 ≠ 0 := by rw [testL_1]; norm_num
  have hF0 : testF (testK 1, testL 1) ≠ 0 := by
    rw [testK_1, testL_1, testF_12]; norm_num
  have h := growthAccounting hY testA_hasDeriv testK_hasDeriv testL_hasDeriv
    testF_hasFDeriv hA0 hK0 hL0 hF0
  rw [testderivA, testderivK, testderivL, testA_1, testK_1, testL_1, testcap,
    testlab] at h
  norm_num at h
  exact h

example : (testA 1 * testF' (1, 0)) * testK 1 / testY 1 = 1 / 3 := by
  have hY : testY 1 = testA 1 * testF (testK 1, testL 1) := rfl
  have hA0 : testA 1 ≠ 0 := by rw [testA_1]; exact one_ne_zero
  have hF0 : testF (testK 1, testL 1) ≠ 0 := by
    rw [testK_1, testL_1, testF_12]; norm_num
  have h := competitiveShare_capital_eq_elasticity (F := testF) (F' := testF')
    hY hA0 hF0
  have hcap : capitalElasticity testF testF' (testK 1) (testL 1) = 1 / 3 := by
    rw [testK_1, testL_1]
    exact testcap
  rw [hcap] at h
  exact h

example : (testA 1 * testF' (0, 1)) * testL 1 / testY 1 = 2 / 3 := by
  have hY : testY 1 = testA 1 * testF (testK 1, testL 1) := rfl
  have hA0 : testA 1 ≠ 0 := by rw [testA_1]; exact one_ne_zero
  have hF0 : testF (testK 1, testL 1) ≠ 0 := by
    rw [testK_1, testL_1, testF_12]; norm_num
  have h := competitiveShare_labour_eq_elasticity (F := testF) (F' := testF')
    hY hA0 hF0
  have hlab : labourElasticity testF testF' (testK 1) (testL 1) = 2 / 3 := by
    rw [testK_1, testL_1]
    exact testlab
  rw [hlab] at h
  exact h

example : (testA 1 * testF' (1, 0)) * testK 1 / testY 1 +
    (testA 1 * testF' (0, 1)) * testL 1 / testY 1 = 1 := by
  have hY : testY 1 = testA 1 * testF (testK 1, testL 1) := rfl
  have hEuler : testF (testK 1, testL 1)
      = testK 1 * testF' (1, 0) + testL 1 * testF' (0, 1) := by
    rw [testK_1, testL_1, testF_12, testFderiv_10, testFderiv_01]
    norm_num
  have hA0 : testA 1 ≠ 0 := by rw [testA_1]; exact one_ne_zero
  have hF0 : testF (testK 1, testL 1) ≠ 0 := by
    rw [testK_1, testL_1, testF_12]; norm_num
  exact competitiveShares_sum_eq_one hY hEuler hA0 hF0

end MathlibExtTest.Economics.Macro.SolowGrowthAccounting
