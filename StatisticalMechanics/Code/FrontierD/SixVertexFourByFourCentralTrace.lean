/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexFourByFourPhysicalBranch
import Code.FrontierD.SixVertexSectorPerronLogConcavity
import Code.FrontierD.SixVertexMarkedTraceParticleHole
import Code.FrontierD.SixVertexBalancedShareVerticalRate
import Code.FrontierD.FKQgt4ParameterBridge

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTrace_particleHole
    {N n : Nat} (hn : n <= N) (M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N (N - n) c ^ M) =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  have hpoly := congrArg (Polynomial.eval (c - 2))
    (sixVertexShiftedSectorTracePolynomial_particleHole hn M)
  simpa [eval_sixVertexShiftedSectorTracePolynomial] using hpoly

theorem sixVertexFourByFour_sectorTrace_logConcave
    (n : Nat) (hn0 : 0 < n) (hn4 : n < 4)
    {c : Real} (hc : 1 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 (n - 1) c ^ 4) *
        Matrix.trace (sixVertexSectorTransfer 4 (n + 1) c ^ 4) <=
      Matrix.trace (sixVertexSectorTransfer 4 n c ^ 4) ^ 2 := by
  obtain ⟨embeddings⟩ :=
    sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors n hn0 hn4
  simpa [sixVertexFourByFourTorus] using
    sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      sixVertexFourByFourTorus
      ⟨n, by norm_num [sixVertexFourByFourTorus]; omega⟩
      hn0 hn4 hc embeddings

theorem sixVertexFourByFour_sectorTrace_le_central
    (n : Nat) (hn : n <= 4) {c : Real} (hc : 1 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 n c ^ 4) <=
      Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) := by
  let a : Nat -> Real := fun sector =>
    Matrix.trace (sixVertexSectorTransfer 4 sector c ^ 4)
  have hcpos : 0 < c := lt_of_lt_of_le Real.zero_lt_one hc
  have hpos : forall sector, sector <= 4 -> 0 < a sector := by
    intro sector hsector
    exact sixVertexSector_trace_pow_pos hsector hcpos 4
  have hsym : forall sector, sector <= 4 -> a (4 - sector) = a sector := by
    intro sector hsector
    exact sixVertexSectorTrace_particleHole hsector 4 c
  have hlc : forall sector, 0 < sector -> sector < 4 ->
      a (sector - 1) * a (sector + 1) <= a sector ^ 2 := by
    intro sector hsector0 hsector4
    exact sixVertexFourByFour_sectorTrace_logConcave
      sector hsector0 hsector4 hc
  change a n <= a 2
  by_cases hn2 : n <= 2
  · exact lowerHalf_le_middle_of_pos_logConcave_symmetric
      a 4 (by norm_num) hpos hsym hlc hn2
  · rw [← hsym n hn]
    apply lowerHalf_le_middle_of_pos_logConcave_symmetric
      a 4 (by norm_num) hpos hsym hlc
    omega

theorem sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum
    {c : Real} (hc : 0 < c) :
    Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) <=
      sixVertexFixedWidthPartitionSum 4 4 c := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces 4 4 (by norm_num)]
  let middle : Fin 5 := ⟨2, by norm_num⟩
  change Matrix.trace (sixVertexSectorTransfer 4 middle.val c ^ 4) <= _
  exact Finset.single_le_sum
    (s := Finset.univ)
    (fun sector (_ : sector ∈ (Finset.univ : Finset (Fin 5))) =>
      (sixVertexSector_trace_pow_pos (by omega) hc 4).le)
    (Finset.mem_univ middle)

theorem sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace
    {c : Real} (hc : 1 <= c) :
    sixVertexFixedWidthPartitionSum 4 4 c <=
      5 * Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces 4 4 (by norm_num)]
  calc
    _ <= ∑ _sector : Fin 5,
        Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) := by
      apply Finset.sum_le_sum
      intro sector _
      exact sixVertexFourByFour_sectorTrace_le_central
        sector.val (by omega) hc
    _ = _ := by simp

theorem sixVertexFourByFour_logPressureGap_mem_Icc
    {c : Real} (hc : 1 <= c) :
    0 <= Real.log (sixVertexFixedWidthPartitionSum 4 4 c) -
        Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4)) ∧
      Real.log (sixVertexFixedWidthPartitionSum 4 4 c) -
          Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4)) <=
        Real.log 5 := by
  have hcpos : 0 < c := lt_of_lt_of_le Real.zero_lt_one hc
  have hcentral : 0 < Matrix.trace
      (sixVertexSectorTransfer 4 2 c ^ 4) :=
    sixVertexSector_trace_pow_pos (by norm_num) hcpos 4
  have hfull : 0 < sixVertexFixedWidthPartitionSum 4 4 c :=
    sixVertexFixedWidthPartitionSum_pos 4 4 (by norm_num) hcpos
  have hlower := Real.log_le_log hcentral
    (sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum hcpos)
  have hupper := Real.log_le_log hfull
    (sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace hc)
  rw [Real.log_mul (by norm_num : (5 : Real) ≠ 0) hcentral.ne'] at hupper
  constructor <;> linarith

theorem sixVertexFourByFour_pressureDensityGap_mem_Icc
    {c : Real} (hc : 1 <= c) :
    0 <= (Real.log (sixVertexFixedWidthPartitionSum 4 4 c) -
          Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4))) / 16 ∧
      (Real.log (sixVertexFixedWidthPartitionSum 4 4 c) -
          Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4))) / 16 <=
        Real.log 5 / 16 := by
  obtain ⟨hlower, hupper⟩ := sixVertexFourByFour_logPressureGap_mem_Icc hc
  constructor <;> linarith

theorem sixVertexFourByFour_balancedTraceShare_mem_Icc
    {c : Real} (hc : 1 <= c) :
    (1 : Real) / 5 <= sixVertexBalancedTraceShare 4 4 c ∧
      sixVertexBalancedTraceShare 4 4 c <= 1 := by
  have hcpos : 0 < c := lt_of_lt_of_le Real.zero_lt_one hc
  have hfull : 0 < sixVertexFixedWidthPartitionSum 4 4 c :=
    sixVertexFixedWidthPartitionSum_pos 4 4 (by norm_num) hcpos
  unfold sixVertexBalancedTraceShare
  norm_num
  constructor
  · rw [le_div_iff₀ hfull]
    have hupper :=
      sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace hc
    linarith
  · rw [div_le_one hfull]
    exact sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum hcpos

theorem fkQgt4_sixVertexFourByFour_noncentralTraceShare_le_four_fifths
    {q : Real} (hq : 4 < q) :
    1 - sixVertexBalancedTraceShare 4 4 (fkQgt4SixVertexWeight q) <=
      (4 : Real) / 5 := by
  have hc : 1 <= fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have hshare :=
    (sixVertexFourByFour_balancedTraceShare_mem_Icc hc).1
  linarith

end

end StatMech.FrontierD
