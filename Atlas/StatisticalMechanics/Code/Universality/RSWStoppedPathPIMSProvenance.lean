/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWAxisGapPIMSAnchoredSide











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section






noncomputable def rlc_sequentialExtremalExteriorEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  StatMech.Percolation.edgesWithinFinset (rlc_strictTopVertices gamma) ∪
    StatMech.Percolation.edgesWithinFinset (rlc_strictBottomVertices gamma')



noncomputable def rlc_sequentialExtremalClosedComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) := fun e =>
  if e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma' then false else omega e





structure RlcSequentialExtremalExplorationState {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) where
  rawConfig : ConfigSpace (Sym2 (Site 2))
  selected : rawConfig ∈ rlc_extremalPairCandidate (gamma, gamma')



noncomputable def RlcSequentialExtremalExplorationState.ofNonempty
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hselected : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    RlcSequentialExtremalExplorationState gamma gamma' where
  rawConfig := Classical.choose hselected
  selected := Classical.choose_spec hselected



theorem rlc_extremalPairCandidateEdges_subset_explored {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_extremalPairCandidateEdges (gamma, gamma') ⊆
      StatMech.Percolation.edgesWithinFinset
          (rlc_rightExploredVertices gamma) ∪
        StatMech.Percolation.edgesWithinFinset
          (rlc_leftExploredVertices gamma') := by
  intro e he
  change e ∈ rlc_rightLowestCandidateEdges gamma ∪
    rlc_leftHighestCandidateEdges gamma' at he
  rw [Finset.mem_union] at he ⊢
  rcases he with he | he
  · exact Or.inl (rlc_rightLowestCandidateEdges_subset gamma he)
  · exact Or.inr (rlc_leftHighestCandidateEdges_subset gamma' he)



@[simp] theorem rlc_sequentialExtremalClosedComparison_of_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} (omega : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma' omega e = false := by
  simp [rlc_sequentialExtremalClosedComparison, he]



theorem rlc_sequentialExtremalClosedComparison_of_not_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} (omega : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma' omega e = omega e := by
  simp [rlc_sequentialExtremalClosedComparison, he]



theorem RlcSequentialExtremalExplorationState.pathPairOpen
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma') :
    S.rawConfig ∈ rlc_pathPairOpen (gamma, gamma') :=
  rlc_extremalPairCandidate_subset_pathPairOpen (gamma, gamma') S.selected



theorem RlcSequentialExtremalExplorationState.rightTrace_open
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges gamma.1) :
    S.rawConfig e = true :=
  S.pathPairOpen.1 e he



theorem RlcSequentialExtremalExplorationState.leftTrace_open
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges gamma'.1) :
    S.rawConfig e = true :=
  S.pathPairOpen.2 e he





structure RlcStoppedExtremalAxisGapProvenance {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) : Prop where
  selectedStratum :
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty
  anchoredSelector :
    RlcAxisGapPIMSAnchoredContourSelector G hn hlt



def RlcStoppedExtremalAxisGapProvenance.ofCandidate {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hselected : omega ∈ rlc_extremalPairCandidate (gamma, gamma'))
    (hselector : RlcAxisGapPIMSAnchoredContourSelector G hn hlt) :
    RlcStoppedExtremalAxisGapProvenance G hn hlt where
  selectedStratum := ⟨omega, hselected⟩
  anchoredSelector := hselector



theorem RlcStoppedExtremalAxisGapProvenance.toExtremalPairCandidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt) :
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty :=
  S.selectedStratum



theorem RlcStoppedExtremalAxisGapProvenance.toFailureSelectedSideTopology
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt) :
    RlcAxisGapPIMSFailureSelectedSideTopology G hn hlt :=
  rlc_axisGapPIMSFailureSelectedSideTopology_of_anchoredContourSelector
    G hn hlt S.anchoredSelector



theorem RlcStoppedExtremalAxisGapProvenance.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau := by
  exact rlc_axisGapPIMSBoundaryArc_of_anchoredSideExists G hn hlt tau
    (S.toFailureSelectedSideTopology tau hno)




theorem RlcStoppedExtremalAxisGapProvenance.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  rlc_axisGapPIMS_success_of_anchoredContourSelector
    G hn hlt S.anchoredSelector tau hno





def RlcExtremalStrataCarryStoppedPIMSProvenance (n : Int) : Prop :=
  ∀ (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper),
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty →
      Nonempty (RlcStoppedExtremalAxisGapProvenance G hn hlt)



theorem rlc_stoppedPIMSProvenance_of_extremalConstruction {n : Int}
    (hconstruction : RlcExtremalStrataCarryStoppedPIMSProvenance n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hselected : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    Nonempty (RlcStoppedExtremalAxisGapProvenance G hn hlt) :=
  hconstruction gamma gamma' G hn hlt hselected

end

end StatMech.Universality
