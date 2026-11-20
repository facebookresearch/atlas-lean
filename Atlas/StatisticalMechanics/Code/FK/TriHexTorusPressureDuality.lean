/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.TriHexTorusComparison

open Finset Set SimpleGraph Filter Topology

namespace StatMech
namespace FK
namespace PeriodicPlanar

theorem triHexTorusPrimalPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < triHexTorusPrimalPartitionSum L p q := by
  unfold triHexTorusPrimalPartitionSum
  exact Finset.sum_pos
    (fun omega _ => FK.fkWeight_pos _ hp hp1 hq omega)
    Finset.univ_nonempty

theorem triHexTorusDualPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {pDual q : ℝ}
    (hp : 0 < pDual) (hp1 : pDual < 1) (hq : 0 < q) :
    0 < triHexTorusDualPartitionSum L pDual q := by
  unfold triHexTorusDualPartitionSum
  exact Finset.sum_pos
    (fun omega _ => FK.fkWeight_pos _ hp hp1 hq
      (triHexTorusDualConfig L omega))
    Finset.univ_nonempty

theorem triHexTorusDefectWeightedDualPartitionSum_pos
    (L : ℕ) [Fact (2 < L)] {pDual q : ℝ}
    (hp : 0 < pDual) (hp1 : pDual < 1) (hq : 0 < q) :
    0 < triHexTorusDefectWeightedDualPartitionSum L pDual q := by
  unfold triHexTorusDefectWeightedDualPartitionSum
  exact Finset.sum_pos (fun omega _ => mul_pos
    (FK.fkWeight_pos _ hp hp1 hq (triHexTorusDualConfig L omega))
    (zpow_pos hq _)) Finset.univ_nonempty



theorem triHexTorus_partitionCorrection_ratio_bounds
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    1 ≤ triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ∧
      triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ q ^ 2 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hD := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hbounds := triHexTorus_defectWeighted_partition_bounds L hp hp1 hq
  constructor
  · rw [le_div_iff₀ hD]
    simpa using hbounds.1
  · rw [div_le_iff₀ hD]
    simpa [mul_comm] using hbounds.2


theorem triHexTorus_partitionCorrection_log_bounds
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    0 ≤ Real.log
        (triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q /
          triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ∧
      Real.log
          (triHexTorusDefectWeightedDualPartitionSum L
              (BeffaraDC.dualParam p q) q /
            triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ≤
        2 * Real.log q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hW := triHexTorusDefectWeightedDualPartitionSum_pos
    L hpDual hpDual1 hq0
  have hD := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hratioPos : 0 <
      triHexTorusDefectWeightedDualPartitionSum L
          (BeffaraDC.dualParam p q) q /
        triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q :=
    div_pos hW hD
  have hb := triHexTorus_partitionCorrection_ratio_bounds L hp hp1 hq
  constructor
  · exact Real.log_nonneg hb.1
  · have hq2 : 0 < q ^ 2 := pow_pos hq0 _
    have hmono := Real.strictMonoOn_log.monotoneOn
      hratioPos hq2 hb.2
    simpa [Real.log_pow] using hmono


noncomputable def triHexTorusPartitionCorrectionLogDensity
    (p q : ℝ) (n : ℕ) : ℝ := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact Real.log
    (triHexTorusDefectWeightedDualPartitionSum L
        (BeffaraDC.dualParam p q) q /
      triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) /
    (L ^ 2 : ℕ)


theorem triHexTorus_partitionCorrection_logDensity_tendsto_zero
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (triHexTorusPartitionCorrectionLogDensity p q)
      atTop (nhds 0) := by
  let C : ℝ := 2 * Real.log q
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.log_nonneg hq)
  have hub : ∀ n : ℕ,
      triHexTorusPartitionCorrectionLogDensity p q n ≤
        C / ((n + 1 : ℕ) : ℝ) := by
    intro n
    let L := n + 3
    letI : Fact (2 < L) := ⟨by simp [L]⟩
    have hlog :=
      (triHexTorus_partitionCorrection_log_bounds L hp hp1 hq).2
    have hden0 : 0 ≤ ((L ^ 2 : ℕ) : ℝ) := by positivity
    have hsmall0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hden : ((n + 1 : ℕ) : ℝ) ≤ ((L ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 ≤ (n + 3) ^ 2 by nlinarith)
    unfold triHexTorusPartitionCorrectionLogDensity
    dsimp only
    calc
      Real.log
          (triHexTorusDefectWeightedDualPartitionSum L
              (BeffaraDC.dualParam p q) q /
            triHexTorusDualPartitionSum L
              (BeffaraDC.dualParam p q) q) /
          ((L ^ 2 : ℕ) : ℝ) ≤ C / ((L ^ 2 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hlog hden0
      _ ≤ C / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hC hsmall0 hden
  have hupper : Tendsto
      (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (Filter.tendsto_add_atTop_nat 1)
  apply squeeze_zero
  · intro n
    let L := n + 3
    letI : Fact (2 < L) := ⟨by simp [L]⟩
    unfold triHexTorusPartitionCorrectionLogDensity
    dsimp only
    exact div_nonneg
      (triHexTorus_partitionCorrection_log_bounds L hp hp1 hq).1
      (by positivity)
  · exact hub
  · exact hupper


noncomputable def triHexTorusPressureDualityResidual
    (L : ℕ) [Fact (2 < L)] (p q : ℝ) : ℝ :=
  let pDual := BeffaraDC.dualParam p q
  let m := (triangularTorusGraph L).edgeFinset.card
  let v := Nat.card (TorusSite L)
  (Real.log (triHexTorusPrimalPartitionSum L p q) +
      (m + 1 : ℝ) * Real.log q -
    ((m : ℝ) * Real.log (p / (1 - pDual)) +
      (v : ℝ) * Real.log q +
      Real.log (triHexTorusDualPartitionSum L pDual q))) /
    (L ^ 2 : ℕ)



theorem triHexTorusPressureDualityResidual_eq_partitionCorrection
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexTorusPressureDualityResidual L p q =
      Real.log
        (triHexTorusDefectWeightedDualPartitionSum L
            (BeffaraDC.dualParam p q) q /
          triHexTorusDualPartitionSum L
            (BeffaraDC.dualParam p q) q) /
        (L ^ 2 : ℕ) := by
  let pDual := BeffaraDC.dualParam p q
  let m := (triangularTorusGraph L).edgeFinset.card
  let v := Nat.card (TorusSite L)
  let PZ := triHexTorusPrimalPartitionSum L p q
  let DZ := triHexTorusDualPartitionSum L pDual q
  let WZ := triHexTorusDefectWeightedDualPartitionSum L pDual q
  let b := p / (1 - pDual)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual : 0 < pDual := BeffaraDC.dualParam_pos hp hp1 hq0
  have hpDual1 : pDual < 1 := BeffaraDC.dualParam_lt_one hp hp1 hq0
  have hb : 0 < b := div_pos hp (sub_pos.mpr hpDual1)
  have hP : 0 < PZ := triHexTorusPrimalPartitionSum_pos L hp hp1 hq0
  have hD : 0 < DZ := triHexTorusDualPartitionSum_pos L hpDual hpDual1 hq0
  have hW : 0 < WZ :=
    triHexTorusDefectWeightedDualPartitionSum_pos L hpDual hpDual1 hq0
  have hpart := triHexTorus_partition_duality_defectWeighted L hp hp1 hq0
  have hpart' : PZ * q ^ (m + 1) = b ^ m * q ^ v * WZ := by
    simpa only [PZ, DZ, WZ, b, pDual, m, v] using hpart
  have hlog := congrArg Real.log hpart'
  rw [Real.log_mul hP.ne' (pow_pos hq0 _).ne', Real.log_pow,
    Real.log_mul (mul_pos (pow_pos hb _) (pow_pos hq0 _)).ne' hW.ne',
    Real.log_mul (pow_pos hb _).ne' (pow_pos hq0 _).ne',
    Real.log_pow, Real.log_pow] at hlog
  have hres :
      Real.log PZ + (m + 1 : ℝ) * Real.log q -
          ((m : ℝ) * Real.log b + (v : ℝ) * Real.log q + Real.log DZ) =
        Real.log (WZ / DZ) := by
    rw [Real.log_div hW.ne' hD.ne']
    push_cast at hlog
    linarith
  unfold triHexTorusPressureDualityResidual
  dsimp only
  change (Real.log PZ + (m + 1 : ℝ) * Real.log q -
      ((m : ℝ) * Real.log b + (v : ℝ) * Real.log q + Real.log DZ)) /
        ((L ^ 2 : ℕ) : ℝ) = _
  rw [hres]




theorem triHexTorusPressureDualityResidual_tendsto_zero
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => (by
      let L := n + 3
      letI : Fact (2 < L) := ⟨by simp [L]⟩
      exact triHexTorusPressureDualityResidual L p q : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply (triHexTorus_partitionCorrection_logDensity_tendsto_zero
    hp hp1 hq).congr'
  filter_upwards [] with n
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact (triHexTorusPressureDualityResidual_eq_partitionCorrection
    L hp hp1 hq).symm

end PeriodicPlanar
end FK
end StatMech
