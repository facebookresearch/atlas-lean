/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWExtremalSelectionObstruction











open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



def RlcAxisGapPIMSPreimagesClosed
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∀ t : ℤ, G.lower ≤ t -> t < G.upper ->
    omega (rlc_pimsEdgeEquiv s(![0, t], ![0, t + 1])) = false




theorem rlc_mixedWiredConnectorEvent_of_axisGapOpen
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : ∀ t : ℤ, G.lower ≤ t -> t < G.upper ->
      omega s(![0, t], ![0, t + 1]) = true) :
    omega ∈ rlc_mixedWiredConnectorEvent G := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let w := sw_vertSeg 0 G.lower G.upper
  let H := openSubgraph 2 eta
  have hw : ∀ e ∈ w.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ p q =>
        have hadj : (hypercubicLattice 2).Adj p q := w.adj_of_mem_edges he
        have hpSupport : p ∈ w.support := w.fst_mem_support_of_mem_edges he
        have hqSupport : q ∈ w.support := w.snd_mem_support_of_mem_edges he
        obtain ⟨tp, htp, hp⟩ :=
          (sw_vertSeg_mem_support 0 G.lower G.upper p).mp hpSupport
        obtain ⟨tq, htq, hq⟩ :=
          (sw_vertSeg_mem_support 0 G.lower G.upper q).mp hqSupport
        rw [Set.uIcc_of_le (le_of_lt G.lower_lt_upper)] at htp htq
        simp only [Set.mem_Icc] at htp htq
        have hdist : (tp - tq).natAbs = 1 := by
          rw [hp, hq, hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          simpa using hadj
        obtain ⟨t, htLower, htUpper, hedge⟩ :
            ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
              s(p, q) = s(![0, t], ![0, t + 1]) := by
          rcases Int.natAbs_eq_iff.mp hdist with hdiff | hdiff <;>
            simp only [Nat.cast_one] at hdiff
          · refine ⟨tq, htq.1, by omega, ?_⟩
            rw [hp, hq, show tp = tq + 1 by omega, Sym2.eq_swap]
          · refine ⟨tp, htp.1, by omega, ?_⟩
            rw [hp, hq, show tq = tp + 1 by omega]
        have hmem : s(![0, t], ![0, t + 1]) ∈
            rlc_mixedAxisGapEdges G :=
          G.verticalEdge_mem_mixedAxisGapEdges hn hlt htLower htUpper
        have hnotPath : s(![0, t], ![0, t + 1]) ∉
            rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 :=
          (Finset.mem_sdiff.mp hmem).2
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨hadj, ?_⟩
        rw [hedge]
        simp [eta, rlc_wiredConnectorConfig, hnotPath,
          rlc_maskConfig, hmem, hopen t htLower htUpper]
  let q : H.Walk ![0, G.lower] ![0, G.upper] := w.transfer H hw
  have hbox : ∀ z ∈ q.support,
      z ∈ rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    have hzW : z ∈ w.support := by
      simpa [q] using hz
    obtain ⟨t, ht, rfl⟩ :=
      (sw_vertSeg_mem_support 0 G.lower G.upper z).mp hzW
    rw [Set.uIcc_of_le (le_of_lt G.lower_lt_upper)] at ht
    simp only [Set.mem_Icc] at ht
    have hlowerBox := rlc_rightPathVertex_mem_connectorBox
      gamma G.lowerVertex_mem_right
    have hupperBox := rlc_leftPathVertex_mem_connectorBox
      gamma' G.upperVertex_mem_left
    simp only [RlcAxisBarrierGap.lowerVertex,
      RlcAxisBarrierGap.upperVertex, mem_rect, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hlowerBox hupperBox
    rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  change ConnectedWithin 2 eta (rect (-2 * n) (2 * n) (-n) n)
    ⟨G.lowerVertex, _⟩ ⟨G.upperVertex, _⟩
  let qbox := q.induce (rect (-2 * n) (2 * n) (-n) n) hbox
  exact ⟨by
    simpa [qbox, q, H, RlcAxisBarrierGap.lowerVertex,
      RlcAxisBarrierGap.upperVertex] using qbox⟩



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hclosed : RlcAxisGapPIMSPreimagesClosed G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_of_axisGapOpen G hn hlt
  intro t htLower htUpper
  rw [rlc_dualReflectConfig_eq_pims, hclosed t htLower htUpper]
  rfl




def RlcAxisOrContactDualConnectorCertificate
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  RlcAxisGapPIMSPreimagesClosed G omega ∨
    (RlcLowestHighestReflectedBoundaryContact G omega ∧
      RlcOuterExitContactArcOrder G omega)



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcert : RlcAxisOrContactDualConnectorCertificate G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  rcases hcert with haxis | ⟨hcontact, horder⟩
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed
      G hn hlt omega haxis
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact
      G hn hlt omega hcontact horder




theorem rlc_mixedWiredConnector_half_of_axisOrContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hcert : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent G ->
        RlcAxisOrContactDualConnectorCertificate G omega) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_mixedWiredConnector_half_of_dual_reflection G
  intro omega hno
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact
    G hn hlt omega (hcert omega hno)




theorem rlc_windingSideCounterexample_contactFree_dual_success :
    rlc_windingSideCounterexampleConfig ∉
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧
      ¬ RlcLowestHighestReflectedBoundaryContact
        rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig ∧
      rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  refine ⟨rlc_windingSideCounterexample_failure,
    rlc_windingSideCounterexample_not_reflectedBoundaryContact, ?_⟩
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed
    rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
  unfold RlcAxisGapPIMSPreimagesClosed
  intro t htLower htUpper
  rfl

end Universality
end StatMech
