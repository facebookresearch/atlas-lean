/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BetacPc

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BetacPc`

* `pToBeta` and `betaToP` at `q = 2` agree with `betaOfP` and `pOfBeta`, and vanish at `0`;
* `betaToP_bijOn` at `q = 3`;
* `betaC` of the step curve `m(β) = 0` for `β ≤ 1`, `m(β) = 1` for `β > 1`, computed directly and
  via `betaC_eq` with `q = 2`, `p_c = pOfBeta 1`, which discharges all hypotheses of `betaC_eq`;
* `magnetization_pos_iff` on the same curve.

The hypotheses of `isingBetaC_eq` are discharged in the test of
`FKRepresentation.PcUpperAllDimensions`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.BetacPc

open _root_.StatMech _root_.StatMech.IsingFK

/-- A step magnetization curve with critical point `1`. -/
noncomputable def stepCurve (β : ℝ) : ℝ := if β ≤ 1 then 0 else 1

-- The `q = 2` parametrization is the Ising one.
example (p : ℝ) : pToBeta 2 p = betaOfP p := pToBeta_two_eq_betaOfP p

-- The `q = 2` inverse parametrization is the Ising one.
example (β : ℝ) : betaToP 2 β = pOfBeta β := betaToP_two_eq_pOfBeta β

-- Both parametrizations fix `0`.
example : pToBeta 3 0 = 0 ∧ betaToP 3 0 = 0 := ⟨pToBeta_zero 3, betaToP_zero 3⟩

-- For `q = 3` the parametrization is a bijection `[0, ∞) → [0, 1)`.
example : Set.BijOn (betaToP 3) (Set.Ici 0) (Set.Ico 0 1) := betaToP_bijOn 3 (by norm_num)

/-- The step curve is nonnegative. -/
lemma stepCurve_nonneg (β : ℝ) : 0 ≤ stepCurve β := by
  unfold stepCurve; split_ifs <;> norm_num

/-- The FK critical value `pOfBeta 1` maps back to `β = 1`. -/
lemma pToBeta_two_pOfBeta_one : pToBeta 2 (pOfBeta 1) = 1 := by
  rw [pToBeta_two_eq_betaOfP, betaOfP_pOfBeta]

/-- The step curve is positive exactly above `pToBeta 2 (pOfBeta 1) = 1`. -/
lemma stepCurve_pos_iff (β : ℝ) (_ : 0 < β) : 0 < stepCurve β ↔ pToBeta 2 (pOfBeta 1) < β := by
  rw [pToBeta_two_pOfBeta_one]
  unfold stepCurve
  split_ifs <;> constructor <;> intro <;> linarith

-- `betaC` of the step curve is `1`, computed from the definition.
example : betaC stepCurve = 1 := by
  unfold betaC
  have hset : {β : ℝ | 0 < β ∧ stepCurve β = 0} = Set.Ioc 0 1 := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_Ioc, stepCurve]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨h0, ?_⟩
      by_contra h
      simp [h] at h1
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by simp [h1]⟩
  rw [hset, csSup_Ioc zero_lt_one]

-- `betaC_eq` applies to the step curve with every hypothesis discharged.
example : betaC stepCurve = 1 := by
  rw [betaC_eq stepCurve 2 (pOfBeta 1) stepCurve_nonneg stepCurve_pos_iff
    (by rw [pToBeta_two_pOfBeta_one]; norm_num), pToBeta_two_pOfBeta_one]

-- `magnetization_pos_iff` on the step curve: at `p = pOfBeta 2` the curve is positive.
example : 0 < stepCurve (pToBeta 2 (pOfBeta 2)) := by
  rw [magnetization_pos_iff stepCurve 2 (pOfBeta 1) (pOfBeta 2) (by norm_num)
    (pOfBeta_mem_Ico 2 (by norm_num)) (pOfBeta_mem_Ico 1 zero_le_one)
    (by rw [pToBeta_two_eq_betaOfP, betaOfP_pOfBeta]; norm_num) stepCurve_pos_iff]
  exact pOfBeta_strictMonoOn (by simp) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.BetacPc
