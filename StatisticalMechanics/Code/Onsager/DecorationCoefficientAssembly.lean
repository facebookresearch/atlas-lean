/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationCycleWeight
import Code.Onsager.DecorationEdgeComponent
import Code.Onsager.TorusIntersection
import Code.Onsager.SpinCoefficientInduction









namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising



theorem ons_decCycle_remainder_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d : ons_Dart L} (q : (ons_decGraph L).Walk d d)
    (hq : q.IsCycle) (R : ons_DecoratedEvenSubgraph L)
    (hzero : ∀ v ∈ q.support, incCount R.1 v = 0) :
    ons_homologyIntersection
        (ons_evenHomology L (ons_walkOriginalEdges q))
        (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) = 0 := by
  classical
  obtain ⟨ι, hiFintype, hiDecidable, base, p, hpcycle,
      hcover, hedgeDisj, hvertDisj⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L R
  letI : Fintype ι := hiFintype
  letI : DecidableEq ι := hiDecidable
  have hhomology :
      ons_evenHomology L (ons_originalEdgesOfDecorated L R) =
        ∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i)) := by
    simpa only [ons_walkOriginalEdges, ons_walkExternalEdges] using
      ons_originalHomology_biUnion R
        (fun i ↦ (p i).edges.toFinset) hcover hedgeDisj
  rw [hhomology]
  rw [show (∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i))) =
      ∑ i ∈ Finset.univ,
        ons_evenHomology L (ons_walkOriginalEdges (p i)) by simp]
  rw [ons_homologyIntersection_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  have hpR : (p i).edges.toFinset ⊆ R.1 := by
    intro edge hedge
    rw [hcover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hedge⟩
  have hverts : Disjoint q.toSubgraph.verts (p i).toSubgraph.verts :=
    ons_cycle_vertices_disjoint_of_incCount_zero
      (ons_decGraph L) q (p i) (hpcycle i) R.1 hzero hpR
  exact ons_decCycles_originalHomology_isotropic
    L q (p i) hq (hpcycle i) hverts




theorem ons_decoratedWeightedSpinWeight_split_eq_neg_cycleWeight
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) (d : ons_Dart L)
    (hd : s(d, ons_dartRev L d) ∈ D.1)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ∃ (q : (ons_decGraph L).Walk d d)
      (R : ons_DecoratedEvenSubgraph L),
      q.IsCycle ∧ q.snd = ons_dartRev L d ∧
      D.1 = q.edges.toFinset ∪ R.1 ∧
      Disjoint q.edges.toFinset R.1 ∧
      (∀ v ∈ q.support, incCount R.1 v = 0) ∧
      incCount R.1 d = 0 ∧
      incCount R.1 (ons_dartRev L d) = 0 ∧
      ons_decoratedWeightedSpinWeight L weight a b D =
        -ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn q) *
          ons_decoratedWeightedSpinWeight L weight a b R := by
  obtain ⟨q, R, hq, hsnd, hsplit, hdisj, hzero, hzeroD, hzeroRev⟩ :=
    ons_decorated_split_cycle_at_external L D d hd
  have hisotropic :=
    ons_decCycle_remainder_originalHomology_isotropic L q hq R hzero
  have hfactor := ons_decoratedWeightedSpinWeight_split_of_isotropic
    L D R q hsplit hdisj weight a b hisotropic
  have hcycle := ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    q hq hsnd weight a b
  refine ⟨q, R, hq, hsnd, hsplit, hdisj, hzero, hzeroD, hzeroRev, ?_⟩
  rw [hfactor, hcycle]
  ring



abbrev ons_DecoratedContainingEdge
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :=
  {D : ons_DecoratedEvenSubgraph L //
    s(d, ons_dartRev L d) ∈ D.1}



structure ons_DecoratedEdgeSplit
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (D : ons_DecoratedContainingEdge L d) where
  cycle : (ons_decGraph L).Walk d d
  remainder : ons_DecoratedEvenSubgraph L
  cycle_isCycle : cycle.IsCycle
  cycle_snd : cycle.snd = ons_dartRev L d
  edge_split : D.1.1 = cycle.edges.toFinset ∪ remainder.1
  edge_disjoint : Disjoint cycle.edges.toFinset remainder.1
  remainder_zero : ∀ v ∈ cycle.support, incCount remainder.1 v = 0
  remainder_zero_root : incCount remainder.1 d = 0
  remainder_zero_rev : incCount remainder.1 (ons_dartRev L d) = 0

noncomputable def ons_decoratedEdgeSplit
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (D : ons_DecoratedContainingEdge L d) :
    ons_DecoratedEdgeSplit L d D := by
  let hex := ons_decorated_split_cycle_at_external L D.1 d D.2
  let q := Classical.choose hex
  let hexR := Classical.choose_spec hex
  let R := Classical.choose hexR
  have hs := Classical.choose_spec hexR
  exact ⟨q, R, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩



theorem ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (d : ons_Dart L) :
    ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L d) =
      ∑ D : ons_DecoratedContainingEdge L d,
        -ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn
              (ons_decoratedEdgeSplit L d D).cycle) *
          ons_decoratedWeightedSpinWeight L weight a b
            (ons_decoratedEdgeSplit L d D).remainder := by
  classical
  rw [ons_weightedSpinEdgeCoefficient_eq_decorated]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun D : ons_DecoratedEvenSubgraph L ↦
      s(d, ons_dartRev L d) ∈ D.1)
    (Finset.univ.filter
      (fun D : ons_DecoratedEvenSubgraph L ↦
        s(d, ons_dartRev L d) ∈ D.1)) (by simp)]
  apply Finset.sum_congr rfl
  intro D hD
  let S := ons_decoratedEdgeSplit L d D
  have hisotropic :=
    ons_decCycle_remainder_originalHomology_isotropic
      L S.cycle S.cycle_isCycle S.remainder S.remainder_zero
  have hfactor := ons_decoratedWeightedSpinWeight_split_of_isotropic
    L D.1 S.remainder S.cycle S.edge_split S.edge_disjoint
      weight a b hisotropic
  have hcycle := ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    S.cycle S.cycle_isCycle S.cycle_snd weight a b
  rw [hfactor, hcycle]
  ring





def ons_decoratedCycleRemovalIdentity (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ (a b : Fin 2)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (d : ons_Dart L),
    ons_detWalkRoot
        (ons_maskMatrix ({d, ons_dartRev L d} : Finset (ons_Dart L))
          (ons_KWmatWeightedPhase L weight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) *
      (∑' s, ons_firstReturnWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        d (ons_dartRev L d) s) =
      ∑ D : ons_DecoratedContainingEdge L d,
        ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn
              (ons_decoratedEdgeSplit L d D).cycle) *
          ons_decoratedWeightedSpinWeight L weight a b
            (ons_decoratedEdgeSplit L d D).remainder



theorem ons_weightedEdgeCoefficientIdentity_of_decoratedCycleRemoval
    (L : ℕ) [Fact (2 < L)]
    (hremove : ons_decoratedCycleRemovalIdentity L) :
    ons_weightedEdgeCoefficientIdentity L := by
  intro a b weight q hq hweight hsmall d
  rw [ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib, ← hremove a b weight d]

end StatMech.Onsager
