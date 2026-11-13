/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.DiscreteBH
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.DiscreteBH

/-! ### A heterogeneous discrete example: two hypotheses, level `α = 1/20`

Hypothesis `0` has an exact p-value with atoms `1/25` (mass `1/25`) and `1`; hypothesis `1` cannot
reach significance below `1/2` (atoms `1/2` and `1`). The overall support is
`A = {0, 1/25, 1/2, 1}`. -/

/-- Null CDF of hypothesis `0`: atoms at `1/25` and `1`. -/
noncomputable def nullCDF0 (t : ℝ) : ℝ := if t < 1 / 25 then 0 else if t < 1 then 1 / 25 else 1

/-- Null CDF of hypothesis `1`: atoms at `1/2` and `1`. -/
noncomputable def nullCDF1 (t : ℝ) : ℝ := if t < 1 / 2 then 0 else if t < 1 then 1 / 2 else 1

/-- The null CDFs of the two hypotheses. -/
noncomputable def Fex : Fin 2 → ℝ → ℝ := ![nullCDF0, nullCDF1]

/-- The overall p-value support. -/
noncomputable def Aex : Finset ℝ := {0, 1 / 25, 1 / 2, 1}

/-- Observed p-values `(1/25, 1)`. -/
noncomputable def pex : Fin 2 → ℝ := ![1 / 25, 1]

/-- The example satisfies the null-CDF hypotheses of the [DBH-SU] FDR theorem. -/
theorem Fex_nonneg (i : Fin 2) (t : ℝ) : 0 ≤ Fex i t := by
  fin_cases i <;>
    simp only [Fex, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, nullCDF0, nullCDF1] <;>
    split_ifs <;> norm_num

/-- Both null CDFs vanish at `0`. -/
theorem Fex_zero (i : Fin 2) : Fex i 0 = 0 := by
  fin_cases i <;> norm_num [Fex, nullCDF0, nullCDF1]

/-- `τ_m = 1/25`: at `t = 1/25` the corrected average is `(1/2)(1/24) = 1/48 ≤ 1/20`, while
`t = 1/2` gives `25/48` and `t = 1` has `F_i(1) = 1`. -/
theorem last_eq : dbhSULastCritical (1 / 20) Fex Aex = 1 / 25 := by
  unfold dbhSULastCritical
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton] at hy
    rcases hy with rfl | ⟨hy, h⟩
    · norm_num
    · rcases hy with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num [Fex, nullCDF0, nullCDF1, Fin.sum_univ_two, Fin.forall_fin_two] at h
      · norm_num [Fex, nullCDF0, nullCDF1, Fin.sum_univ_two, Fin.forall_fin_two] at h
  · apply Finset.le_max'
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
    norm_num [Fex, nullCDF0, nullCDF1, Fin.sum_univ_two, Fin.forall_fin_two]

/-- `τ_1 = 1/25`, larger than the BH critical value `α · 1 / m = 1/40`. -/
theorem crit_one : dbhSUCritical (1 / 20) Fex Aex 1 = 1 / 25 := by
  unfold dbhSUCritical
  simp only [last_eq]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_filter] at hy
    rcases hy with rfl | ⟨-, hy, -⟩
    · norm_num
    · exact hy
  · apply Finset.le_max'
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
    norm_num [Fex, nullCDF0, nullCDF1, Fin.sum_univ_two]

/-- `τ_2 = 1/25`. -/
theorem crit_two : dbhSUCritical (1 / 20) Fex Aex 2 = 1 / 25 := by
  unfold dbhSUCritical
  simp only [last_eq]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_filter] at hy
    rcases hy with rfl | ⟨-, hy, -⟩
    · norm_num
    · exact hy
  · apply Finset.le_max'
    simp only [Aex, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
    norm_num [Fex, nullCDF0, nullCDF1, Fin.sum_univ_two]

private theorem numBelow_pex : numBelow pex (1 / 25) = 1 := by
  rw [numBelow, show (Finset.univ.filter fun i => pex i ≤ 1 / 25) = {0} by
    ext i; fin_cases i <;> norm_num [pex]]
  rfl

/-- The [DBH-SU] step-up index is `1`: one p-value is at most `τ_1 = 1/25`, but not two are at
most `τ_2 = 1/25`. -/
theorem stepUpIndex_dbhSU : stepUpIndex (dbhSUCritical (1 / 20) Fex Aex) pex = 1 := by
  have hge : 1 ≤ stepUpIndex (dbhSUCritical (1 / 20) Fex Aex) pex :=
    le_stepUpIndex (by norm_num) (by rw [crit_one, numBelow_pex])
  have hne : stepUpIndex (dbhSUCritical (1 / 20) Fex Aex) pex ≠ 2 := by
    intro h
    have := stepUpIndex_le_numBelow (dbhSUCritical (1 / 20) Fex Aex) pex
    rw [h, crit_two, numBelow_pex] at this
    omega
  have hle := stepUpIndex_le (dbhSUCritical (1 / 20) Fex Aex) pex
  omega

/-- [DBH-SU] at level `1/20` rejects hypothesis `0`. -/
theorem dbhSURejections_pex : dbhSURejections (1 / 20) Fex Aex pex = {0} := by
  ext i
  simp only [dbhSURejections, Finset.mem_filter, Finset.mem_univ, true_and, stepUpIndex_dbhSU,
    crit_one]
  fin_cases i <;> norm_num [pex]

/-- BH at the same level `1/20` rejects nothing: `1/25 > 1/40` and only one p-value is at most
`2/40`. -/
theorem bhRejections_pex : bhRejections (1 / 20) pex = ∅ := by
  have h1 : numBelow pex (1 / 20 * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 0 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      pex i ≤ 1 / 20 * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ∅ by
        ext i; fin_cases i <;> norm_num [pex]]
    rfl
  have h2 : numBelow pex (1 / 20 * ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 1 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      pex i ≤ 1 / 20 * ((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = {0} by
        ext i; fin_cases i <;> norm_num [pex]]
    rfl
  have hidx : bhIndex (1 / 20) pex = 0 := by
    have hle := bhIndex_le (1 / 20) pex
    have hnum := bhIndex_le_numBelow (1 / 20) pex
    interval_cases h : bhIndex (1 / 20) pex
    · rfl
    · rw [h1] at hnum; omega
    · rw [h2] at hnum; omega
  ext i
  simp only [bhRejections, Finset.mem_filter, Finset.mem_univ, true_and, hidx]
  fin_cases i <;> norm_num [pex]

/-- **Non-vacuity of the sharpening**: on this discrete example [DBH-SU] rejects strictly more
than BH at the same level. -/
theorem bhRejections_ssubset_dbhSURejections :
    bhRejections (1 / 20) pex ⊂ dbhSURejections (1 / 20) Fex Aex pex := by
  rw [bhRejections_pex, dbhSURejections_pex]
  exact Finset.empty_ssubset.mpr ⟨0, Finset.mem_singleton_self 0⟩

/-! ### The shifted leave-one-out identity on a concrete vector

With `c k = k / 4`, `m = 3` and `p = (1/10, 1/5, 4/5)`, `p 2 = 4/5 > c 3 = 3/4`. Both sides of
`stepUpIndex_update_eq_shift` are computed from the definitions: replacing `p 2` by `0` gives
step-up index `3`, and the shifted critical values `(c 2, c 3, c 3) = (1/2, 3/4, 3/4)` give `2`. -/

/-- The p-values of the shift example. -/
noncomputable def pshift : Fin 3 → ℝ := ![1 / 10, 1 / 5, 4 / 5]

theorem stepUpIndex_update_pshift :
    stepUpIndex (fun k : ℕ => (k : ℝ) / 4) (Function.update pshift 2 0) = 3 := by
  refine le_antisymm (stepUpIndex_le _ _) (le_stepUpIndex le_rfl ?_)
  rw [numBelow, show (Finset.univ.filter fun i =>
      Function.update pshift 2 0 i ≤ ((3 : ℕ) : ℝ) / 4) = Finset.univ by
    ext i; fin_cases i <;> norm_num [pshift, Function.update]]
  rfl

theorem stepUpIndex_shift_pshift :
    stepUpIndex (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift = 2 := by
  have h34 : (Finset.univ.filter fun i => pshift i ≤ ((3 : ℕ) : ℝ) / 4) = {0, 1} := by
    ext i; fin_cases i <;> norm_num [pshift]
  have hge : 2 ≤ stepUpIndex (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift := by
    apply le_stepUpIndex (by norm_num)
    rw [show min (2 + 1) 3 = 3 from rfl, numBelow, h34]
    rfl
  have hne : stepUpIndex (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift ≠ 3 := by
    intro h
    have := stepUpIndex_le_numBelow (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift
    rw [h, show min (3 + 1) 3 = 3 from rfl, numBelow, h34] at this
    exact absurd this (by decide)
  have hle := stepUpIndex_le (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift
  omega

/-- The two computed sides agree with `stepUpIndex_update_eq_shift`: `3 = 2 + 1`. -/
example : stepUpIndex (fun k : ℕ => (k : ℝ) / 4) (Function.update pshift 2 0) =
    stepUpIndex (fun k : ℕ => ((min (k + 1) 3 : ℕ) : ℝ) / 4) pshift + 1 := by
  rw [stepUpIndex_update_pshift, stepUpIndex_shift_pshift]

/-! ### Axioms of the main theorems -/

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.integral_falseDiscoveryProportion_dbhSURejections_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_falseDiscoveryProportion_dbhSURejections_le

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.integral_falseDiscoveryProportion_stepUp_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_falseDiscoveryProportion_stepUp_le

/--
info: 'MathlibExt.Probability.Statistics.MultipleTesting.integral_falseDiscoveryProportion_stepUp_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_falseDiscoveryProportion_stepUp_le_sum

end MathlibExtTest.Probability.Statistics.MultipleTesting.DiscreteBH
