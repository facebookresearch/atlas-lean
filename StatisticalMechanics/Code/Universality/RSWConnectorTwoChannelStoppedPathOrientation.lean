/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation
import Code.Universality.RSWStoppedPathPIMSProvenance











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section




structure RlcStoppedTwoChannelOrientedCommonCycleState
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') where
  provenance : RlcStoppedExtremalAxisGapProvenance G hn hlt
  anchor : Site 2
  contour : (faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk anchor anchor
  contour_isCycle : contour.IsCycle
  contour_orientation :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega =
      jec_leftRegion (contour.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))
  candidate_obstruction :
    ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
        gamma gamma' omega contour z



noncomputable def rlc_stoppedTwoChannelOrientedCommonCycleState_of_noGood
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega := by
  let H :=
    rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle
      gamma gamma' hfaith omega hno hnoGood
  let u := H.choose
  let c := H.choose_spec.choose
  have hspec := H.choose_spec.choose_spec
  exact ⟨S, u, c, hspec.1, hspec.2.1, hspec.2.2⟩



def RlcStoppedTwoChannelOrientedCandidateStateAt
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (z : Site 2) : Prop :=
  z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
    RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
      gamma gamma' omega X.contour z


theorem RlcStoppedTwoChannelOrientedCommonCycleState.candidateState
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
    RlcStoppedTwoChannelOrientedCandidateStateAt X z :=
  ⟨hz, X.candidate_obstruction z hz⟩



theorem
    RlcStoppedTwoChannelOrientedCommonCycleState.candidateTransition
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    (rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q,
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
          RlcStoppedTwoChannelOrientedCandidateStateAt X q) ∨
      ∃ q,
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          RlcStoppedTwoChannelOrientedCandidateStateAt X q := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition
        hzCandidate hyPath hflipLeftRank hbracket with
    hfixed | ⟨q, hqCandidate, hqz⟩ | ⟨q, hqCandidate, hzq⟩
  · exact Or.inl hfixed
  · exact Or.inr (Or.inl ⟨q, hqz, X.candidateState hqCandidate⟩)
  · exact Or.inr (Or.inr ⟨q, hzq, X.candidateState hqCandidate⟩)



theorem RlcStoppedTwoChannelOrientedCommonCycleState.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau :=
  X.provenance.boundaryArc_of_failure tau hno



theorem RlcStoppedTwoChannelOrientedCommonCycleState.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  X.provenance.pims_success_of_failure tau hno


theorem RlcStoppedTwoChannelOrientedCandidateStateAt.boundaryArc_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcAxisGapPIMSBoundaryArc G hn hlt tau :=
  X.boundaryArc_of_failure tau hno



theorem RlcStoppedTwoChannelOrientedCandidateStateAt.pims_success_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (_hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  X.pims_success_of_failure tau hno




def RlcStoppedTwoChannelCandidateResolved
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G


theorem RlcStoppedTwoChannelOrientedCandidateStateAt.resolved_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
  exact Or.inr (hz.pims_success_of_failure X tau hno)



theorem RlcStoppedTwoChannelOrientedCommonCycleState.no_unresolved_candidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    ¬(¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∧
      rlc_axisGapPIMSReflectedConfig G tau ∉
        rlc_finiteAxisGapConnectorEvent G) := by
  rintro ⟨_hnoGood, hnoSuccess⟩
  exact hnoSuccess (hz.pims_success_of_failure X tau hno)




theorem rlc_stoppedTwoChannel_good_or_pimsSuccess_of_failures
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hnoTwoChannel : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGap : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
  by_cases hgood : RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega
  · exact Or.inl hgood
  · let X := rlc_stoppedTwoChannelOrientedCommonCycleState_of_noGood
      G hn hlt S hfaith omega hnoTwoChannel hgood
    exact Or.inr (X.pims_success_of_failure tau hnoGap)

end

end StatMech.Universality
