/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.DiscreteBHAdaptive

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.DiscreteBHAdaptive

/-! ### `maxSubsetSum` is a top-`r` sum, not the full sum

For `x = (3, 1, 2)` the largest single coordinate is `3`, while the full sum is `6`. -/

example : maxSubsetSum ![(3 : ℝ), 1, 2] 1 = 3 := by
  refine le_antisymm (maxSubsetSum_le fun S hS => ?_) ?_
  · calc ∑ i ∈ S, ![(3 : ℝ), 1, 2] i ≤ ∑ _i ∈ S, (3 : ℝ) :=
          Finset.sum_le_sum fun i _ => by fin_cases i <;> norm_num
      _ = S.card * 3 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * 3 := by gcongr; exact_mod_cast hS
      _ = 3 := by norm_num
  · simpa using sum_le_maxSubsetSum ![(3 : ℝ), 1, 2] (S := {0}) (r := 1) (by simp)

/-! ### Three discrete hypotheses at level `α = 1/4`

Each hypothesis has an exact p-value with atoms `1/10` (mass `1/10`), `1/5` (mass `1/10`) and `1`,
so `F(t) = t` on the support `A = {1/10, 1/5, 1}`. The observed p-values are `(1/5, 1/5, 1)`.
All critical values below are computed from the definitions.

* `τ_3 = 1/5` for both procedures: `F(1/5) / (1 - F(1/5)) = 1/4 ≤ α`, and `F(1) = 1`.
* [DBH-SU]: `τ_2 = 1/10`, since the full sum `3 F(t) / (4/5)` must be at most `2 α = 1/2`;
  `τ_1 = 0`. No `k` has `k` p-values below `τ_k`, so nothing is rejected.
* [A-DBH-SU]: `τ_2 = 1/5`, since only the `3 - 2 + 1 = 2` largest terms enter:
  `2 · (1/5) / (4/5) = 1/2 ≤ 1/2`. Two p-values are at most `1/5`, so both are rejected. -/

/-- The null CDF shared by the three hypotheses: atoms at `1/10`, `1/5` and `1`. -/
noncomputable def nullCDF (t : ℝ) : ℝ :=
  if t < 1 / 10 then 0 else if t < 1 / 5 then 1 / 10 else if t < 1 then 1 / 5 else 1

/-- The null CDFs of the three hypotheses. -/
noncomputable def Fex : Fin 3 → ℝ → ℝ := fun _ => nullCDF

/-- The overall p-value support. -/
noncomputable def Aex : Finset ℝ := {1 / 10, 1 / 5, 1}

/-- Observed p-values `(1/5, 1/5, 1)`. -/
noncomputable def pex : Fin 3 → ℝ := ![1 / 5, 1 / 5, 1]

theorem nullCDF_tenth : nullCDF (1 / 10) = 1 / 10 := by norm_num [nullCDF]

theorem nullCDF_fifth : nullCDF (1 / 5) = 1 / 5 := by norm_num [nullCDF]

theorem nullCDF_one : nullCDF 1 = 1 := by norm_num [nullCDF]

/-- The example satisfies the null-CDF hypotheses of the [A-DBH-SU] FDR theorem. -/
theorem Fex_nonneg (i : Fin 3) (t : ℝ) : 0 ≤ Fex i t := by
  simp only [Fex, nullCDF]
  split_ifs <;> norm_num

/-- The null CDFs vanish at `0`. -/
theorem Fex_zero (i : Fin 3) : Fex i 0 = 0 := by norm_num [Fex, nullCDF]

/-- `τ_3 = 1/5`. -/
theorem last_eq : dbhSULastCritical (1 / 4) Fex Aex = 1 / 5 := by
  unfold dbhSULastCritical
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton] at hy
    rcases hy with rfl | ⟨hy, h⟩
    · norm_num
    · rcases hy with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact absurd (h.1 0) (by norm_num [Fex, nullCDF_one])
  · apply Finset.le_max'
    refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨by simp [Aex], ?_, ?_⟩)
    · intro i
      norm_num [Fex, nullCDF_fifth]
    · norm_num [Fex, nullCDF_fifth, Fin.sum_univ_three]

/-- [DBH-SU]: `τ_2 = 1/10`. -/
theorem dbh_two : dbhSUCritical (1 / 4) Fex Aex 2 = 1 / 10 := by
  unfold dbhSUCritical
  simp only [last_eq]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton] at hy
    rcases hy with rfl | ⟨hy, h₁, h₂⟩
    · norm_num
    · rcases hy with rfl | rfl | rfl
      · norm_num
      · norm_num [Fex, nullCDF_fifth, Fin.sum_univ_three] at h₂
      · norm_num at h₁
  · apply Finset.le_max'
    refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨by simp [Aex], by norm_num, ?_⟩)
    norm_num [Fex, nullCDF_tenth, nullCDF_fifth, Fin.sum_univ_three]

/-- [DBH-SU]: `τ_1 = 0`. -/
theorem dbh_one : dbhSUCritical (1 / 4) Fex Aex 1 = 0 := by
  refine le_antisymm ?_ (dbhSUCritical_nonneg 1)
  unfold dbhSUCritical
  simp only [last_eq]
  apply Finset.max'_le
  intro y hy
  simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton] at hy
  rcases hy with rfl | ⟨hy, h₁, h₂⟩
  · norm_num
  · rcases hy with rfl | rfl | rfl
    · norm_num [Fex, nullCDF_tenth, nullCDF_fifth, Fin.sum_univ_three] at h₂
    · norm_num [Fex, nullCDF_fifth, Fin.sum_univ_three] at h₂
    · norm_num at h₁

private theorem numBelow_fifth : numBelow pex (1 / 5) = 2 := by
  rw [numBelow, show (Finset.univ.filter fun i => pex i ≤ 1 / 5) = {0, 1} by
    ext i; fin_cases i <;> norm_num [pex]]
  rfl

private theorem numBelow_tenth : numBelow pex (1 / 10) = 0 := by
  rw [numBelow, show (Finset.univ.filter fun i => pex i ≤ 1 / 10) = ∅ by
    ext i; fin_cases i <;> norm_num [pex]]
  rfl

private theorem numBelow_zero : numBelow pex 0 = 0 := by
  rw [numBelow, show (Finset.univ.filter fun i => pex i ≤ 0) = ∅ by
    ext i; fin_cases i <;> norm_num [pex]]
  rfl

/-- The [DBH-SU] step-up index is `0`. -/
theorem stepUpIndex_dbhSU : stepUpIndex (dbhSUCritical (1 / 4) Fex Aex) pex = 0 := by
  have hle := stepUpIndex_le (dbhSUCritical (1 / 4) Fex Aex) pex
  have hnum := stepUpIndex_le_numBelow (dbhSUCritical (1 / 4) Fex Aex) pex
  interval_cases h : stepUpIndex (dbhSUCritical (1 / 4) Fex Aex) pex
  · rfl
  · rw [dbh_one, numBelow_zero] at hnum; omega
  · rw [dbh_two, numBelow_tenth] at hnum; omega
  · rw [dbhSUCritical_self, last_eq, numBelow_fifth] at hnum; omega

/-- [DBH-SU] at level `1/4` rejects nothing. -/
theorem dbhSURejections_pex : dbhSURejections (1 / 4) Fex Aex pex = ∅ := by
  have h0 : dbhSUCritical (1 / 4) Fex Aex 0 = 0 :=
    le_antisymm ((monotone_dbhSUCritical (by norm_num) (Nat.zero_le 1)).trans_eq dbh_one)
      (dbhSUCritical_nonneg 0)
  ext i
  simp only [dbhSURejections, Finset.mem_filter, Finset.mem_univ, true_and, stepUpIndex_dbhSU,
    h0]
  fin_cases i <;> norm_num [pex]

/-- [A-DBH-SU]: `τ_2 = 1/5`. Every set of at most `3 - 2 + 1 = 2` hypotheses has corrected sum at
most `2 · (1/5) / (4/5) = 1/2 = 2 α`. -/
theorem adbh_two : adbhSUCritical (1 / 4) Fex Aex 2 = 1 / 5 := by
  refine le_antisymm ((adbhSUCritical_le_last 2).trans_eq last_eq) ?_
  have hmax : maxSubsetSum (fun i : Fin 3 => Fex i (1 / 5) / (1 - Fex i (1 / 5))) (3 - 2 + 1) ≤
      1 / 2 := maxSubsetSum_le fun S hS => by
    have hS2 : S.card ≤ 2 := by simpa using hS
    calc ∑ i ∈ S, Fex i (1 / 5) / (1 - Fex i (1 / 5)) = ∑ _i ∈ S, (1 / 4 : ℝ) :=
          Finset.sum_congr rfl fun i _ => by norm_num [Fex, nullCDF_fifth]
      _ = S.card * (1 / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (1 / 4) := by gcongr; exact_mod_cast hS2
      _ = 1 / 2 := by norm_num
  unfold adbhSUCritical
  simp only [last_eq]
  apply Finset.le_max'
  refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨by simp [Aex], le_rfl, ?_⟩)
  refine (mul_le_mul_of_nonneg_left hmax (by positivity)).trans (le_of_eq ?_)
  norm_num

/-- The [A-DBH-SU] step-up index is `2`. -/
theorem stepUpIndex_adbhSU : stepUpIndex (adbhSUCritical (1 / 4) Fex Aex) pex = 2 := by
  have hge : 2 ≤ stepUpIndex (adbhSUCritical (1 / 4) Fex Aex) pex :=
    le_stepUpIndex (by norm_num) (by rw [adbh_two, numBelow_fifth])
  have hne : stepUpIndex (adbhSUCritical (1 / 4) Fex Aex) pex ≠ 3 := by
    intro h
    have h3 := stepUpIndex_le_numBelow (adbhSUCritical (1 / 4) Fex Aex) pex
    rw [h] at h3
    have hmono := numBelow_mono pex ((adbhSUCritical_le_last (α := 1 / 4) (F := Fex) (A := Aex)
      3).trans_eq last_eq)
    rw [numBelow_fifth] at hmono
    omega
  have hle := stepUpIndex_le (adbhSUCritical (1 / 4) Fex Aex) pex
  omega

/-- [A-DBH-SU] at level `1/4` rejects hypotheses `0` and `1`. -/
theorem adbhSURejections_pex : adbhSURejections (1 / 4) Fex Aex pex = {0, 1} := by
  ext i
  simp only [adbhSURejections, Finset.mem_filter, Finset.mem_univ, true_and, stepUpIndex_adbhSU,
    adbh_two]
  fin_cases i <;> norm_num [pex]

/-- **Non-vacuity of the adaptivity**: on this example [A-DBH-SU] rejects strictly more than
[DBH-SU] at the same level. -/
theorem dbhSURejections_ssubset_adbhSURejections :
    dbhSURejections (1 / 4) Fex Aex pex ⊂ adbhSURejections (1 / 4) Fex Aex pex := by
  rw [dbhSURejections_pex, adbhSURejections_pex]
  exact Finset.empty_ssubset.mpr ⟨0, by simp⟩

/-! ### Axioms of the main theorems -/

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.integral_falseDiscoveryProportion_adbhSURejections_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_falseDiscoveryProportion_adbhSURejections_le

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.integral_falseDiscoveryProportion_stepUp_le_adaptive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_falseDiscoveryProportion_stepUp_le_adaptive

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.dbhSURejections_subset_adbhSURejections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dbhSURejections_subset_adbhSURejections

end MathlibExtTest.Probability.Statistics.MultipleTesting.DiscreteBHAdaptive
