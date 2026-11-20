/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingNormalizedPartitionLimit
import Code.FrontierA.QuantumIsingLieTrotter
import Code.FrontierA.QuantumIsingFieldGauge
import Code.FrontierA.QuantumIsingQuantumFreeEnergy
import Code.FrontierC.IsingTransfer










open Filter Matrix
open scoped Topology

namespace StatMech.FrontierA



noncomputable def quantumIsingFiniteFreeEnergy
    (beta h : Real) (L : Nat) : Real :=
  -Real.log ‖quantumIsingQuantumPartition beta h L‖ / beta / L



theorem quantumIsingPeriodicTrotterFreeEnergy_tendsto_finiteQuantum
    (beta h : Real) (L : Nat) (hL : L ≠ 0)
    (hbeta : 0 < beta) (hbh : 0 < beta * h) :
    Tendsto (fun n : Nat ↦
      quantumIsingPeriodicTrotterAction beta h (n + 1) L / L) atTop
      (nhds (quantumIsingFiniteFreeEnergy beta h L)) := by
  have htrace := quantumIsingTrotterTrace_tendsto_quantumPartition beta h L
  have hpath : Tendsto (fun n : Nat ↦
      (quantumIsingTrotterPathPartition beta h (n + 1) L : Complex)) atTop
      (nhds (quantumIsingQuantumPartition beta h L)) := by
    apply htrace.congr'
    filter_upwards with n
    rw [quantumIsingTrotterTrace_eq_pathPartition beta h (n + 1) L (by omega)]
  have hpathPos (n : Nat) :
      0 < quantumIsingTrotterPathPartition beta h (n + 1) L := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
    exact quantumIsingTrotterPathPartition_pos beta h (n + 1) M
      (by omega) hbeta hbh
  have hh : 0 < h := by
    rcases (mul_pos_iff.mp hbh) with hpos | hneg
    · exact hpos.2
    · linarith [hneg.1]
  have hnorm : Tendsto (fun n : Nat ↦
      quantumIsingTrotterPathPartition beta h (n + 1) L) atTop
      (nhds ‖quantumIsingQuantumPartition beta h L‖) := by
    have h := (continuous_norm.tendsto
      (quantumIsingQuantumPartition beta h L)).comp hpath
    convert h using 1
    funext n
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hpathPos n)]
  have hlog : Tendsto (fun n : Nat ↦
      Real.log (quantumIsingTrotterPathPartition beta h (n + 1) L)) atTop
      (nhds (Real.log ‖quantumIsingQuantumPartition beta h L‖)) :=
    (Real.continuousAt_log
      (quantumIsingQuantumPartition_norm_pos beta h L hbeta hh).ne').tendsto.comp hnorm
  have hscaled := hlog.neg.div_const beta |>.div_const (L : Real)
  apply hscaled.congr'
  filter_upwards with n
  rw [quantumIsingPeriodicTrotterAction_eq_log_pathPartition
    beta h (n + 1) L hL]



theorem quantumIsingFiniteFreeEnergy_sub_value_le
    (beta h : Real) (L : Nat) (hL : L ≠ 0)
    (hbeta : 0 < beta) (hh : 0 < h) :
    |quantumIsingFiniteFreeEnergy beta h L -
      quantumIsingFreeEnergyValue beta h| ≤ 1 / (2 * (L : Real)) := by
  have hbh : 0 < beta * h := mul_pos hbeta hh
  have hfinite :=
    (quantumIsingPeriodicTrotterFreeEnergy_tendsto_finiteQuantum
      beta h L hL hbeta hbh).comp (tendsto_add_atTop_nat 2)
  have hcofinal := quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto
    beta h hbeta hh
  have hdiff := hfinite.sub hcofinal
  have habs := hdiff.abs
  apply le_of_tendsto habs
  filter_upwards with n
  simpa only [Function.comp_apply, Nat.add_assoc, Nat.reduceAdd,
    abs_sub_comm] using
    (quantumIsingPeriodicTrotterFreeEnergy_uniform_bound
      beta h (n + 3) (by omega) hbeta hbh (L := L) hL)



theorem quantumIsingFiniteFreeEnergy_tendsto_of_pos
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr : Tendsto (fun L : Nat ↦ 1 / (2 * (L : Real))) atTop
      (nhds 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : Real) using 1
    funext L
    ring
  apply squeeze_zero' (Eventually.of_forall fun L ↦ norm_nonneg _) ?_ herr
  filter_upwards [eventually_gt_atTop 0] with L hL
  simpa only [Real.norm_eq_abs] using
    quantumIsingFiniteFreeEnergy_sub_value_le beta h L
      (Nat.ne_of_gt hL) hbeta hh

theorem quantumIsingFiniteFreeEnergy_neg_field
    (beta h : Real) (L : Nat) :
    quantumIsingFiniteFreeEnergy beta (-h) L =
      quantumIsingFiniteFreeEnergy beta h L := by
  unfold quantumIsingFiniteFreeEnergy
  rw [quantumIsingQuantumPartition_neg_field]



theorem quantumIsingFiniteFreeEnergy_tendsto_of_ne_zero
    (beta h : Real) (hbeta : 0 < beta) (hh : h ≠ 0) :
    Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  rcases lt_or_gt_of_ne hh with hhneg | hhpos
  · have ht := quantumIsingFiniteFreeEnergy_tendsto_of_pos
      beta (-h) hbeta (neg_pos.mpr hhneg)
    rw [quantumIsingFreeEnergyValue_neg beta h] at ht
    exact ht.congr' (Eventually.of_forall fun L ↦
      quantumIsingFiniteFreeEnergy_neg_field beta h L)
  · exact quantumIsingFiniteFreeEnergy_tendsto_of_pos beta h hbeta hhpos

end StatMech.FrontierA
