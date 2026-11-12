/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSignedPhysical
import Code.FrontierA.TriangularIsingGeneralSymbol









namespace StatMech.FrontierA



theorem triangularTorusIsingPartition_freeEnergy_first_lipschitz
    (J1 K1 J2 J3 : Real) (n : Nat) :
    |(-Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2) -
      (-Real.log (triangularTorusIsingPartitionSequence K1 J2 J3 n) /
          (n + 3 : Real) ^ 2)| ≤ |J1 - K1| := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  have hlog := ZJ_log_coupling_sub_abs_le
    (triangularTorusGraph L).edgeFinset
    (triangularTorusRealEdgeWeight L J1 J2 J3)
    (triangularTorusRealEdgeWeight L K1 J2 J3)
  rw [sum_abs_triangularTorusRealEdgeWeight_sub] at hlog
  have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
  unfold triangularTorusIsingPartitionSequence
  rw [← sub_div, abs_div, abs_of_pos hden]
  calc
    |-Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0)) -
        -Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L K1 J2 J3) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 =
      |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L K1 J2 J3) (fun _ => 0)) -
        Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 := by
      congr 2
      ring
    _ ≤ ((L * L : Nat) * (|J1 - K1| + |J2 - J2| + |J3 - J3|)) /
          (n + 3 : Real) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa only [abs_sub_comm] using hlog
    _ = |J1 - K1| := by
      dsimp only [L]
      norm_num only [sub_self, abs_zero, add_zero, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]
      field_simp




theorem triangularTorusIsingPartition_freeEnergy_tendsto_general
    (J1 J2 J3 : Real) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
  let finiteFreeEnergy : Real → Nat → Real := fun K1 n =>
    -Real.log (triangularTorusIsingPartitionSequence K1 J2 J3 n) /
      (n + 3 : Real) ^ 2
  let freeEnergy : Real → Real := fun K1 =>
    triangularIsingFreeEnergyValue K1 J2 J3
  have hcontinuous : ContinuousAt freeEnergy J1 := by
    have hmap : ContinuousAt (fun K1 : Real => (K1, (J2, J3))) J1 :=
      continuousAt_id.prodMk (continuousAt_const.prodMk continuousAt_const)
    have hcomp := continuous_triangularIsingFreeEnergyValue.continuousAt.comp hmap
    simpa only [freeEnergy, Function.comp_apply] using hcomp
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hclose⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous) (epsilon / 3) (by positivity)
  let eta := min delta (epsilon / 3)
  have heta : 0 < eta := lt_min hdelta (by positivity)
  obtain ⟨K1, hK1close, hK1pos⟩ :=
    exists_triangularIsingSymbol_pos_approx_first J1 J2 J3 eta heta
  have hK1delta : dist K1 J1 < delta := by
    rw [Real.dist_eq]
    exact hK1close.trans_le (min_le_left _ _)
  have hvalue : dist (freeEnergy K1) (freeEnergy J1) < epsilon / 3 :=
    hclose hK1delta
  have hboundary : |J1 - K1| < epsilon / 3 := by
    rw [abs_sub_comm]
    exact hK1close.trans_le (min_le_right _ _)
  have hpositiveLimit :=
    triangularTorusIsingPartition_freeEnergy_tendsto_signed
      K1 J2 J3 triangularKacWardPhaseRoot
      triangularKacWardPhaseRoot_pow_four hK1pos
  rw [Metric.tendsto_atTop] at hpositiveLimit
  obtain ⟨N, hN⟩ := hpositiveLimit (epsilon / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hfiniteBound :=
    triangularTorusIsingPartition_freeEnergy_first_lipschitz
      J1 K1 J2 J3 n
  have hfinite : dist (finiteFreeEnergy J1 n) (finiteFreeEnergy K1 n) <
      epsilon / 3 := by
    rw [Real.dist_eq]
    exact hfiniteBound.trans_lt hboundary
  have hbulk : dist (finiteFreeEnergy K1 n) (freeEnergy K1) < epsilon / 3 := by
    simpa only [finiteFreeEnergy, freeEnergy] using hN n hn
  change dist (finiteFreeEnergy J1 n) (freeEnergy J1) < epsilon
  calc
    dist (finiteFreeEnergy J1 n) (freeEnergy J1) ≤
        dist (finiteFreeEnergy J1 n) (finiteFreeEnergy K1 n) +
          dist (finiteFreeEnergy K1 n) (freeEnergy J1) :=
      dist_triangle _ _ _
    _ ≤ dist (finiteFreeEnergy J1 n) (finiteFreeEnergy K1 n) +
        (dist (finiteFreeEnergy K1 n) (freeEnergy K1) +
          dist (freeEnergy K1) (freeEnergy J1)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < epsilon := by linarith

end StatMech.FrontierA
