/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.EdgeSubsetDomainMarkov
import Code.FK.BoundaryEdgeAbsorption
import Code.FK.ConditionalFibreMass
import Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Code.Universality.RSWSequentialStoppedConditionalLaw









open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


def rlc_twoChannelActiveEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :=
  FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma') ⁻¹'
    rlc_finiteTwoChannelConnectorEvent gamma gamma'


theorem rlc_twoChannelActiveEvent_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.restrictActive (rlc_connectorTwoChannelGraph gamma gamma') ⁻¹'
        rlc_twoChannelActiveEvent gamma gamma' =
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  ext rho
  change
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma')
            (FK.restrictActive
              (rlc_connectorTwoChannelGraph gamma gamma') rho))).Reachable x y) ↔
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho).Reachable x y
  rw [FK.openSub_extendActive_restrictActive_eq]



structure RlcTwoChannelCompatibleExteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop where
  twoChannel_le : rlc_connectorTwoChannelGraph gamma gamma' ≤ H
  trace_le : rlc_connectorTraceWiring gamma gamma' ≤ H
  trace_open : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
    psi e = true

theorem RlcTwoChannelCompatibleExteriorFibre.trace_le_frozenExterior
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorTraceWiring gamma gamma' ≤
      FK.edgeSubsetFrozenExteriorGraph
        (rlc_connectorTwoChannelGraph gamma gamma') H B psi := by
  intro x y hxy
  left
  refine ⟨F.trace_le hxy, ?_, F.trace_open s(x, y) ?_⟩
  · intro htwo
    exact htwo.2 hxy
  · rw [SimpleGraph.mem_edgeFinset]
    exact hxy



theorem RlcTwoChannelCompatibleExteriorFibre.separate_le_inducedWiring
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorSeparateWiring gamma gamma' ≤
      FK.edgeSubsetInducedWiring
        (rlc_connectorTwoChannelGraph gamma gamma') H B psi := by
  intro x y hxy
  rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hxy
  refine ⟨?_, ?_⟩
  · rcases hxy with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact hright.1
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact hleft.1
  · rcases hxy with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact (rlc_connectorTraceWiring_reachable_right gamma gamma'
        hright.2.1 hright.2.2).mono (F.trace_le_frozenExterior B)
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact (rlc_connectorTraceWiring_reachable_left gamma gamma'
        hleft.2.1 hleft.2.2).mono (F.trace_le_frozenExterior B)


theorem rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') ≤
      FK.edgeSubsetFibreCondEventMass
        (rlc_connectorTwoChannelGraph gamma gamma') H B psi
        (BeffaraDC.selfDualPoint q) q
        (rlc_twoChannelActiveEvent gamma gamma') := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [FK.edgeSubsetFibreCondEventMass_eq_bcEventMass
      (rlc_connectorTwoChannelGraph gamma gamma') H B
      F.twoChannel_le psi hp hp1 hq0,
    rlc_twoChannelActiveEvent_preimage]
  exact FK.bcProb_mono_bc
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (FK.edgeSubsetInducedWiring
      (rlc_connectorTwoChannelGraph gamma gamma') H B psi)
    (F.separate_le_inducedWiring B) hp hp1 hq
    (rlc_finiteTwoChannelConnectorEvent_isIncreasing gamma gamma')



theorem
    rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 ≤ q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) ≤
      FK.edgeSubsetFibreCondEventMass
        (rlc_connectorTwoChannelGraph gamma gamma') H B psi
        (BeffaraDC.selfDualPoint q) q
        (rlc_twoChannelActiveEvent gamma gamma') := by
  exact (rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut
    hinc hstatic hq N hscore).trans
      (rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate
        gamma gamma' H B psi F hq)



theorem rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (F : RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 ≤ q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho ∈ FK.condFibre
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
      ∑ rho ∈ FK.condFibre
        (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let c := 1 / (1 + (Real.sqrt q) ^ N * q)
  let mass := ∑ rho ∈ FK.condFibre
    (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi,
    FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  have hcond : c ≤
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q
            (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi rho := by
    calc
      c ≤ FK.edgeSubsetFibreCondEventMass
          (rlc_connectorTwoChannelGraph gamma gamma') H B psi
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelActiveEvent gamma gamma') :=
        rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut
          H B psi F hinc hstatic hq N hscore
      _ = _ := by
        rw [FK.edgeSubsetFibreCondEventMass_eq_ambientSum,
          rlc_twoChannelActiveEvent_preimage]
  rw [FK.condBcProb_event_fibre_eq_mass_mul_cond
    H B hp hp1 hq0
    (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset psi
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')]
  change c * mass ≤ mass * _
  rw [mul_comm c mass]
  exact mul_le_mul_of_nonneg_left hcond
    (Finset.sum_nonneg fun rho _ => FK.bcProb_nonneg H B hp hp1 hq0 rho)




theorem rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    (hS : FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset S)
    (hcompat : ∀ {psi}, psi ∈ S →
      RlcTwoChannelCompatibleExteriorFibre gamma gamma' H psi)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 ≤ q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩ S).indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let K := rlc_connectorTwoChannelGraph gamma gamma'
  let F := K.edgeFinset
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let c := 1 / (1 + (Real.sqrt q) ^ N * q)
  change c *
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  rw [FK.bcProb_fibre_decompose H B hp hp1 hq0 F (A ∩ S),
    FK.bcProb_fibre_decompose H B hp hp1 hq0 F S,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [FK.fibreReps, Finset.mem_filter] at hpsi
  let mass := ∑ sigma ∈ FK.condFibre F psi,
    FK.bcProb H B (BeffaraDC.selfDualPoint q) q sigma
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun sigma _ =>
    FK.bcProb_nonneg H B hp hp1 hq0 sigma
  have hScond :
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi :=
    FK.condBcProb_sum_outside H B hp hp1 hq0 hS hpsi.2
  have hAScond :
      (∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi *
          (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) :=
    FK.condBcProb_cross_outside H B hS
  rw [hScond, hAScond]
  by_cases hpsiS : psi ∈ S
  · have hlocal :=
      rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut
        H B psi (hcompat hpsiS) hinc hstatic hq N hscore
    rw [FK.edgeSubsetFibreCondEventMass_eq_ambientSum,
      rlc_twoChannelActiveEvent_preimage] at hlocal
    change c ≤
      ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho at hlocal
    rw [Set.indicator_of_mem hpsiS]
    simp only [mul_one, one_mul]
    change c * mass ≤ mass *
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho)
    calc
      c * mass = mass * c := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal hmass
  · simp [Set.indicator_of_notMem hpsiS]



theorem rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset) :
    FK.DependsOnOutside
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset
      (rlc_finiteExtremalPairCandidate gamma gamma') := by
  intro psi rho hagree
  apply indic_iff
  apply rlc_finiteExtremalPairCandidate_dependsOn
  intro e he
  exact (hagree e (fun heK =>
    (Finset.disjoint_left.mp hdisj) he heK)).symm




theorem
    rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : rlc_connectorTwoChannelGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset)
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 ≤ q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ rho,
          (rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
      ∑ rho,
        (rlc_finiteTwoChannelConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  apply rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut
    gamma gamma' H B (rlc_finiteExtremalPairCandidate gamma gamma')
    (rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel
      gamma gamma' hdisj)
    (fun {psi} hpsi =>
      { twoChannel_le := hKH
        trace_le := hTH
        trace_open := rlc_finiteExtremalPairCandidate_trace_open
          gamma gamma' hpsi })
    hinc hstatic hq N hscore

end

end StatMech.Universality
