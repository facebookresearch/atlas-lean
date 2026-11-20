/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWSequentialStoppedExplorationBridge
import Code.Universality.RSWConnectorSeededMassCapstone
import Code.FK.ActiveBoundaryEquiv
import Code.FK.BoundaryEdgeAbsorption
import Code.FK.FKDisjointBoxDomainMarkov












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section




noncomputable def rlc_connectorForcedTraceActiveWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) : Real :=
  FK.fkWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G p q
    (rlc_connectorForceTraceConfig gamma gamma'
      (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta))


noncomputable def rlc_connectorForcedTraceActiveZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ eta, rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta



noncomputable def rlc_connectorForcedTraceActiveProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) : Real :=
  rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta /
    rlc_connectorForcedTraceActiveZ gamma gamma' p q




theorem rlc_connectorForcedTraceActiveWeight_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
  rw [rlc_connectorForcedTraceActiveWeight,
    rlc_fkWeight_augmented_forceTrace_eq_separateBC]
  rfl



theorem rlc_connectorForcedTraceActiveZ_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorForcedTraceActiveZ gamma gamma' p q =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q := by
  unfold rlc_connectorForcedTraceActiveZ
  simp_rw [rlc_connectorForcedTraceActiveWeight_eq_separate]
  rw [← Finset.mul_sum]
  rfl




theorem rlc_connectorForcedTraceActiveProb_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForcedTraceActiveProb gamma gamma' p q eta =
      FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
  unfold rlc_connectorForcedTraceActiveProb FK.activeBCProb
  rw [rlc_connectorForcedTraceActiveWeight_eq_separate,
    rlc_connectorForcedTraceActiveZ_eq_separate]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hp.ne')


def rlc_connectorActiveEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :=
  FK.extendActive (rlc_connectorFiniteGraph gamma gamma') ⁻¹'
    rlc_finiteConnectorEvent gamma gamma'


noncomputable def rlc_connectorForcedTraceActiveEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ eta,
    (rlc_connectorActiveEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
      rlc_connectorForcedTraceActiveProb gamma gamma' p q eta



theorem rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) :
    rlc_connectorForcedTraceActiveEventMass gamma gamma' p q =
      FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q
        (rlc_connectorActiveEvent gamma gamma') := by
  unfold rlc_connectorForcedTraceActiveEventMass FK.activeBCProbOf
    FK.activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorForcedTraceActiveProb_eq_separate gamma gamma' hp eta]



theorem rlc_connectorActiveEvent_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') ⁻¹'
        rlc_connectorActiveEvent gamma gamma' =
      rlc_finiteConnectorEvent gamma gamma' := by
  ext tau
  simp only [Set.mem_preimage, rlc_connectorActiveEvent]
  unfold rlc_finiteConnectorEvent
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  rw [FK.openSub_extendActive_restrictActive_eq]



theorem rlc_connectorForcedTraceActiveEventMass_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedTraceActiveEventMass gamma gamma' p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  rw [rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate
      gamma gamma' hp,
    FK.activeBCProbOf_eq_bcProb_preimage
      (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq,
    rlc_connectorActiveEvent_preimage]
  rfl





noncomputable def rlc_connectorTraceFibreInside {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (RlcConnectorVertex n)) :=
  (rlc_connectorFiniteGraph gamma gamma').edgeFinset



noncomputable def rlc_connectorTraceFibreConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorForceTraceConfig gamma gamma'
    (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta)


noncomputable def rlc_connectorTraceFibreReference {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorTraceFibreConfig gamma gamma' (fun _ => false)



theorem rlc_connectorTraceFibreConfig_agreesOff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma')
      (rlc_connectorTraceFibreReference gamma gamma')
      (rlc_connectorTraceFibreConfig gamma gamma' eta) := by
  intro e he
  by_cases htrace : e ∈
      (rlc_connectorTraceWiring gamma gamma').edgeFinset
  · simp [rlc_connectorTraceFibreReference,
      rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig, htrace]
  · have hnotG : e ∉
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      intro heG
      apply he
      exact SimpleGraph.mem_edgeFinset.mpr heG
    simp [rlc_connectorTraceFibreReference,
      rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
      FK.extendActive, htrace, hnotG]



@[simp] theorem rlc_connectorTraceFibreConfig_restrictActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorTraceFibreConfig gamma gamma' eta) = eta := by
  funext e
  unfold FK.restrictActive rlc_connectorTraceFibreConfig
  rw [rlc_connectorForceTraceConfig_finiteEdge]
  exact FK.extendActive_apply _ _ _



theorem rlc_connectorTraceFibreConfig_restrictActive_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hrho : FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma')
      (rlc_connectorTraceFibreReference gamma gamma') rho) :
    rlc_connectorTraceFibreConfig gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) =
      rho := by
  funext e
  by_cases heG : e ∈
      (rlc_connectorFiniteGraph gamma gamma').edgeSet
  · have hnotTrace : e ∉
        (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
      intro htrace
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hG : (rlc_connectorFiniteGraph gamma gamma').Adj x y :=
            (SimpleGraph.mem_edgeSet _).mp heG
          have hT : (rlc_connectorTraceWiring gamma gamma').Adj x y :=
            (SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp htrace)
          exact rlc_connectorFiniteGraph_adj_not_traceWiring
            gamma gamma' hG hT
    simp [rlc_connectorTraceFibreConfig,
      rlc_connectorForceTraceConfig, hnotTrace, FK.extendActive,
      FK.restrictActive, heG]
  · have heFin : e ∉ rlc_connectorTraceFibreInside gamma gamma' := by
      simpa [rlc_connectorTraceFibreInside,
        SimpleGraph.mem_edgeFinset] using heG
    rw [hrho e heFin]
    by_cases htrace : e ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
    · simp [rlc_connectorTraceFibreReference,
        rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
        htrace]
    · simp [rlc_connectorTraceFibreReference,
        rlc_connectorTraceFibreConfig, rlc_connectorForceTraceConfig,
        FK.extendActive, htrace, heG]



noncomputable def rlc_connectorTraceFibreEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∈ FK.condFibre (rlc_connectorTraceFibreInside gamma gamma')
          (rlc_connectorTraceFibreReference gamma gamma')} where
  toFun eta := ⟨rlc_connectorTraceFibreConfig gamma gamma' eta, by
    rw [FK.mem_condFibre]
    exact rlc_connectorTraceFibreConfig_agreesOff gamma gamma' eta⟩
  invFun rho := FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho.1
  left_inv eta := rlc_connectorTraceFibreConfig_restrictActive gamma gamma' eta
  right_inv rho := by
    apply Subtype.ext
    exact rlc_connectorTraceFibreConfig_restrictActive_eq gamma gamma'
      (FK.mem_condFibre.mp rho.2)



theorem rlc_connectorTraceFibre_bcWeight_bot_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.bcWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
      rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta := by
  change FK.edgeProduct
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorTraceFibreConfig gamma gamma' eta) *
      q ^ FK.numClustersBC
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n))
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
    FK.edgeProduct (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorTraceFibreConfig gamma gamma' eta) *
      q ^ FK.numClusters
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta)
  rw [FK.numClustersBC]
  have hbot : FK.openSub
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta) ⊔
      (⊥ : SimpleGraph (RlcConnectorVertex n)) =
      FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorTraceFibreConfig gamma gamma' eta) := by
    ext x y
    simp
  rw [hbot, FK.numClusters, Nat.card_eq_fintype_card]

set_option maxHeartbeats 800000 in



theorem rlc_connectorTraceFibre_inducedBcZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.inducedBcZ (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreInside gamma gamma')
        (rlc_connectorTraceFibreReference gamma gamma') =
      rlc_connectorForcedTraceActiveZ gamma gamma' p q := by
  unfold FK.inducedBcZ rlc_connectorForcedTraceActiveZ
  let S := FK.condFibre (rlc_connectorTraceFibreInside gamma gamma')
    (rlc_connectorTraceFibreReference gamma gamma')
  let weight := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    FK.bcWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G
      (⊥ : SimpleGraph (RlcConnectorVertex n)) p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((rlc_connectorTraceFibreEquiv gamma gamma') eta) :=
      (Equiv.sum_comp (rlc_connectorTraceFibreEquiv gamma gamma')
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, rlc_connectorForcedTraceActiveWeight
        gamma gamma' p q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact rlc_connectorTraceFibre_bcWeight_bot_eq gamma gamma' p q eta



theorem rlc_connectorTraceFibre_condBcProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.condBcProb (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreInside gamma gamma')
        (rlc_connectorTraceFibreReference gamma gamma')
        (rlc_connectorTraceFibreConfig gamma gamma' eta) =
      rlc_connectorForcedTraceActiveProb gamma gamma' p q eta := by
  unfold FK.condBcProb
  split
  · rw [rlc_connectorTraceFibre_inducedBcZ_eq]
    rw [rlc_connectorTraceFibre_bcWeight_bot_eq]
    rfl
  · rename_i h
    exact (h (rlc_connectorTraceFibreConfig_agreesOff gamma gamma' eta)).elim



noncomputable def rlc_connectorTraceFibreCondEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ eta,
    (rlc_connectorActiveEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
      FK.condBcProb (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (⊥ : SimpleGraph (RlcConnectorVertex n)) p q
        (rlc_connectorTraceFibreInside gamma gamma')
        (rlc_connectorTraceFibreReference gamma gamma')
        (rlc_connectorTraceFibreConfig gamma gamma' eta)


theorem rlc_connectorTraceFibreCondEventMass_eq_forcedTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorTraceFibreCondEventMass gamma gamma' p q =
      rlc_connectorForcedTraceActiveEventMass gamma gamma' p q := by
  unfold rlc_connectorTraceFibreCondEventMass
    rlc_connectorForcedTraceActiveEventMass
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorTraceFibre_condBcProb_eq]




theorem rlc_connectorTraceFibreCondEventMass_eq_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorTraceFibreCondEventMass gamma gamma' p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  rw [rlc_connectorTraceFibreCondEventMass_eq_forcedTrace,
    rlc_connectorForcedTraceActiveEventMass_eq_separate
      gamma gamma' hp hp1 hq]



theorem rlc_connectorTraceFibreCondEventMass_selfDual_ge_one_div_one_add_q
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      rlc_connectorTraceFibreCondEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [rlc_connectorTraceFibreCondEventMass_eq_separate
    gamma gamma' hp hp1 hq0]
  exact rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq hdual






noncomputable def rlc_connectorFrozenExteriorGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (H.Adj x y ∧
      ¬ (rlc_connectorFiniteGraph gamma gamma').Adj x y ∧
      psi s(x, y) = true) ∨ B.Adj x y
  symm := by
    rintro x y (hxy | hxy)
    · left
      exact ⟨hxy.1.symm, fun hyx => hxy.2.1 hyx.symm,
        by simpa [Sym2.eq_swap] using hxy.2.2⟩
    · exact Or.inr hxy.symm
  loopless := ⟨by
    rintro x (hxx | hxx)
    · exact (H.ne_of_adj hxx.1) rfl
    · exact (B.ne_of_adj hxx) rfl⟩

noncomputable instance rlc_connectorFrozenExteriorGraphDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    DecidableRel
      (rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Adj :=
  Classical.decRel _



noncomputable def rlc_connectorExteriorInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := x ≠ y ∧
    (rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Reachable x y
  symm := by
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

noncomputable instance rlc_connectorExteriorInducedWiringDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    DecidableRel
      (rlc_connectorExteriorInducedWiring gamma gamma' H B psi).Adj :=
  Classical.decRel _





noncomputable def rlc_connectorExtendConfig {n : Int}
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  Function.extend
    (Sym2.map (Subtype.val : RlcConnectorVertex n → Site 2)) psi
    (fun _ => false)

@[simp] theorem rlc_connectorExtendConfig_apply {n : Int}
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorExtendConfig psi (e.map Subtype.val) = psi e := by
  exact (Sym2.map.injective Subtype.val_injective).extend_apply _ _ _



theorem rlc_extremalPairCandidateEdge_exists_connectorLift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_extremalPairCandidateEdges (gamma, gamma')) :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' he
  rw [Finset.mem_union] at hexplored
  rcases hexplored with hright | hleft
  · rw [mem_edgesWithinFinset] at hright
    obtain ⟨x, hx, y, hy, rfl⟩ := hright
    have hx' : x ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hx
      rw [rlc_mem_rectFinset, mem_rect] at hx
      rw [mem_rect]
      omega
    have hy' : y ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hy
      rw [rlc_mem_rectFinset, mem_rect] at hy
      rw [mem_rect]
      omega
    exact ⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), by simp⟩
  · rw [mem_edgesWithinFinset] at hleft
    obtain ⟨x, hx, y, hy, rfl⟩ := hleft
    have hx' : x ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hx
      rw [rlc_mem_rectFinset, mem_rect] at hx
      rw [mem_rect]
      omega
    have hy' : y ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hy
      rw [rlc_mem_rectFinset, mem_rect] at hy
      rw [mem_rect]
      omega
    exact ⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), by simp⟩



noncomputable def rlc_finiteExtremalPairCandidateEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (RlcConnectorVertex n)) :=
  Finset.univ.filter fun e =>
    e.map Subtype.val ∈ rlc_extremalPairCandidateEdges (gamma, gamma')



noncomputable def rlc_finiteExtremalPairCandidate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  rlc_connectorExtendConfig ⁻¹'
    rlc_extremalPairCandidate (gamma, gamma')



theorem rlc_finiteExtremalPairCandidate_dependsOn {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    _root_.DependsOn
      ((rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)))
      (rlc_finiteExtremalPairCandidateEdges gamma gamma' :
        Set (Sym2 (RlcConnectorVertex n))) := by
  intro psi rho hagree
  apply rlc_extremalPairCandidate_dependsOn
  intro e he
  obtain ⟨f, rfl⟩ :=
    rlc_extremalPairCandidateEdge_exists_connectorLift gamma gamma' he
  rw [rlc_connectorExtendConfig_apply, rlc_connectorExtendConfig_apply]
  exact hagree f (by
    have he' : f.map Subtype.val ∈
        rlc_extremalPairCandidateEdges (gamma, gamma') := he
    simp [rlc_finiteExtremalPairCandidateEdges, he'])



theorem rlc_connectorRestrictConfig_mem_finiteExtremalPairCandidate_iff
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorRestrictConfig omega ∈
        rlc_finiteExtremalPairCandidate gamma gamma' ↔
      omega ∈ rlc_extremalPairCandidate (gamma, gamma') := by
  change rlc_connectorExtendConfig (rlc_connectorRestrictConfig omega) ∈
      rlc_extremalPairCandidate (gamma, gamma') ↔
    omega ∈ rlc_extremalPairCandidate (gamma, gamma')
  apply indic_iff
  apply rlc_extremalPairCandidate_dependsOn
  intro e he
  obtain ⟨f, rfl⟩ :=
    rlc_extremalPairCandidateEdge_exists_connectorLift gamma gamma' he
  rw [rlc_connectorExtendConfig_apply]
  rfl



theorem rlc_finiteExtremalPairCandidate_dependsOnOutside {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset) :
    FK.DependsOnOutside
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset
      (rlc_finiteExtremalPairCandidate gamma gamma') := by
  intro psi rho hagree
  apply indic_iff
  apply rlc_finiteExtremalPairCandidate_dependsOn
  intro e he
  exact (hagree e (fun heG =>
    (Finset.disjoint_left.mp hdisj) he heG)).symm



theorem rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges gamma gamma')) :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have heCandidate' : e.map Subtype.val ∈
      rlc_extremalPairCandidateEdges (gamma, gamma') :=
    (Finset.mem_filter.mp heCandidate).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heConnector
      exact (Finset.disjoint_left.mp hdisj)
        (by simpa [Sym2.map_mk] using heCandidate') heConnector.2



theorem rlc_finiteExtremalPairCandidate_trace_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
      psi e = true := by
  intro e he
  have hselected : rlc_connectorExtendConfig psi ∈
      rlc_extremalPairCandidate (gamma, gamma') := hpsi
  have hopen := rlc_extremalPairCandidate_subset_pathPairOpen
    (gamma, gamma') hselected
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      rcases Finset.mem_union.mp he.2 with hright | hleft
      · have := hopen.1 s((x : Site 2), (y : Site 2)) hright
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using this
      · have := hopen.2 s((x : Site 2), (y : Site 2)) hleft
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using this



structure RlcConnectorCompatibleExteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop where
  connector_le : rlc_connectorFiniteGraph gamma gamma' ≤ H
  trace_le : rlc_connectorTraceWiring gamma gamma' ≤ H
  trace_open : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
    psi e = true



theorem RlcBookFaithfulTracePair.origin_mem_strictTopSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_strictTopSet gamma := by
  have hn : 0 < n := by
    have hstart := gamma.1.1.2
    rw [mem_leftSide, mem_rect] at hstart
    have hneg := hfaith.right_axis_strict
    omega
  let N := n.toNat
  have hN : (N : Int) = n := Int.toNat_of_nonneg (le_of_lt hn)
  let v : Nat → Site 2 := fun k => ![0, (k : Int)]
  have hvNotPath : ∀ k : Nat, v k ∉ rlc_pathVertices gamma.1 := by
    intro k hk
    have heq := hfaith.right_axis_unique hk (by simp [v])
    have hy := congrArg (fun z : Site 2 => z 1) heq
    simp [v] at hy
    exact (not_lt_of_ge (Int.natCast_nonneg k))
      (hy ▸ hfaith.right_axis_strict)
  have hvRect : ∀ k : Nat, k ≤ N →
      v k ∈ rect 0 (2 * n) (-n) n := by
    intro k hk
    rw [mem_rect]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk' : (k : Int) ≤ n := by
      rw [← hN]
      exact Int.ofNat_le.mpr hk
    omega
  have hreach : ∀ k : Nat, k ≤ N →
      (rlc_rightPathAvoidGraph gamma).Reachable (v 0) (v k) := by
    intro k hk
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
        have hadj : (rlc_rightPathAvoidGraph gamma).Adj (v k) (v (k + 1)) := by
          refine ⟨?_, hvRect k hkN, hvRect (k + 1) hk,
            hvNotPath k, hvNotPath (k + 1)⟩
          simp [v, hypercubicLattice_adj, Fin.sum_univ_two]
        exact (ih hkN).trans hadj.reachable
  let top : Site 2 := ![0, n]
  have htopSide : top ∈ topSide 0 (2 * n) (-n) n := by
    simp [top, mem_topSide, mem_rect, le_of_lt hn]
  have htopNot : top ∉ rlc_pathVertices gamma.1 := by
    simpa [top, v, hN] using hvNotPath N
  have htopOrigin : (rlc_rightPathAvoidGraph gamma).Reachable top (origin 2) := by
    have h := (hreach N (le_refl N)).symm
    have ht : v N = top := by
      ext i
      fin_cases i <;> simp [v, top, hN]
    have ho : v 0 = origin 2 := by
      ext i
      fin_cases i <;> simp [v, origin]
    simpa [ht, ho] using h
  exact ⟨top, htopSide, htopNot, htopOrigin⟩



theorem RlcBookFaithfulTracePair.origin_mem_strictBottomSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    origin 2 ∈ rlc_strictBottomSet gamma' := by
  have hn : 0 < n := by
    have hend := gamma'.1.2.1.2
    rw [mem_rightSide, mem_rect] at hend
    have hpos := hfaith.left_axis_strict
    omega
  let N := n.toNat
  have hN : (N : Int) = n := Int.toNat_of_nonneg (le_of_lt hn)
  let v : Nat → Site 2 := fun k => ![0, -(k : Int)]
  have hvNotPath : ∀ k : Nat, v k ∉ rlc_pathVertices gamma'.1 := by
    intro k hk
    have heq := hfaith.left_axis_unique hk (by simp [v])
    have hy := congrArg (fun z : Site 2 => z 1) heq
    simp [v] at hy
    exact (not_lt_of_ge (neg_nonpos.mpr (Int.natCast_nonneg k)))
      (hy ▸ hfaith.left_axis_strict)
  have hvRect : ∀ k : Nat, k ≤ N →
      v k ∈ rect (-2 * n) 0 (-n) n := by
    intro k hk
    rw [mem_rect]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hk' : (k : Int) ≤ n := by
      rw [← hN]
      exact Int.ofNat_le.mpr hk
    omega
  have hreach : ∀ k : Nat, k ≤ N →
      (rlc_leftPathAvoidGraph gamma').Reachable (v 0) (v k) := by
    intro k hk
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
        have hadj : (rlc_leftPathAvoidGraph gamma').Adj (v k) (v (k + 1)) := by
          refine ⟨?_, hvRect k hkN, hvRect (k + 1) hk,
            hvNotPath k, hvNotPath (k + 1)⟩
          simp [v, hypercubicLattice_adj, Fin.sum_univ_two]
        exact (ih hkN).trans hadj.reachable
  let bottom : Site 2 := ![0, -n]
  have hbottomSide : bottom ∈ bottomSide (-2 * n) 0 (-n) n := by
    simp [bottom, mem_bottomSide, mem_rect, le_of_lt hn]
  have hbottomNot : bottom ∉ rlc_pathVertices gamma'.1 := by
    simpa [bottom, v, hN] using hvNotPath N
  have hbottomOrigin :
      (rlc_leftPathAvoidGraph gamma').Reachable bottom (origin 2) := by
    have h := (hreach N (le_refl N)).symm
    have hb : v N = bottom := by
      ext i
      fin_cases i <;> simp [v, bottom, hN]
    have ho : v 0 = origin 2 := by
      ext i
      fin_cases i <;> simp [v, origin]
    simpa [hb, ho] using h
  exact ⟨bottom, hbottomSide, hbottomNot, hbottomOrigin⟩


def rlc_connectorFoldRight (z : Site 2) : Site 2 :=
  if 0 ≤ z 0 then z else rlc_flipX z


def rlc_connectorFoldLeft (z : Site 2) : Site 2 :=
  if z 0 ≤ 0 then z else rlc_flipX z

theorem rlc_connectorFoldRight_adj {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (hypercubicLattice 2).Adj
      (rlc_connectorFoldRight x) (rlc_connectorFoldRight y) := by
  by_cases hx : 0 ≤ x 0 <;> by_cases hy : 0 ≤ y 0 <;>
    simp [rlc_connectorFoldRight, hx, hy, rlc_flipX, rlc_flipXFun,
      hypercubicLattice_adj, Fin.sum_univ_two] at hxy ⊢ <;> omega

theorem rlc_connectorFoldLeft_adj {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (hypercubicLattice 2).Adj
      (rlc_connectorFoldLeft x) (rlc_connectorFoldLeft y) := by
  by_cases hx : x 0 ≤ 0 <;> by_cases hy : y 0 ≤ 0 <;>
    simp [rlc_connectorFoldLeft, hx, hy, rlc_flipX, rlc_flipXFun,
      hypercubicLattice_adj, Fin.sum_univ_two] at hxy ⊢ <;> omega

theorem rlc_connectorFoldRight_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldRight z ∈ rect 0 (2 * n) (-n) n := by
  have hzBox := (Finset.mem_sdiff.mp hz).1
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  by_cases hz0 : 0 ≤ z 0
  · rw [rlc_connectorFoldRight, if_pos hz0, mem_rect]
    exact ⟨hz0, hzBox.2⟩
  · simp [rlc_connectorFoldRight, hz0, rlc_flipX, rlc_flipXFun,
      mem_rect]
    omega

theorem rlc_connectorFoldLeft_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldLeft z ∈ rect (-2 * n) 0 (-n) n := by
  have hzBox := (Finset.mem_sdiff.mp hz).1
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  by_cases hz0 : z 0 ≤ 0
  · rw [rlc_connectorFoldLeft, if_pos hz0, mem_rect]
    exact ⟨hzBox.1, hz0, hzBox.2.2⟩
  · simp [rlc_connectorFoldLeft, hz0, rlc_flipX, rlc_flipXFun,
      mem_rect]
    omega

theorem rlc_connectorFoldRight_not_path {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldRight z ∉ rlc_pathVertices gamma.1 := by
  have hzNotBarrier := (Finset.mem_sdiff.mp hz).2
  by_cases hz0 : 0 ≤ z 0
  · rw [rlc_connectorFoldRight, if_pos hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hzPath))
  · rw [rlc_connectorFoldRight, if_neg hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    apply Or.inl
    apply Or.inr
    exact Finset.mem_image.mpr
      ⟨rlc_flipX z, hzPath, rlc_flipX_involutive z⟩

theorem rlc_connectorFoldLeft_not_path {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldLeft z ∉ rlc_pathVertices gamma'.1 := by
  have hzNotBarrier := (Finset.mem_sdiff.mp hz).2
  by_cases hz0 : z 0 ≤ 0
  · rw [rlc_connectorFoldLeft, if_pos hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hzPath))
  · rw [rlc_connectorFoldLeft, if_neg hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    apply Or.inr
    exact Finset.mem_image.mpr
      ⟨rlc_flipX z, hzPath, rlc_flipX_involutive z⟩



noncomputable def rlc_connectorFoldRightHom {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).induce
        (rlc_connectorAllowed gamma gamma' : Set (Site 2)) →g
      rlc_rightPathAvoidGraph gamma where
  toFun z := rlc_connectorFoldRight z
  map_rel' := by
    intro x y hxy
    refine ⟨rlc_connectorFoldRight_adj hxy,
      rlc_connectorFoldRight_mem_rect gamma gamma' x.2,
      rlc_connectorFoldRight_mem_rect gamma gamma' y.2,
      rlc_connectorFoldRight_not_path gamma gamma' x.2,
      rlc_connectorFoldRight_not_path gamma gamma' y.2⟩


noncomputable def rlc_connectorFoldLeftHom {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).induce
        (rlc_connectorAllowed gamma gamma' : Set (Site 2)) →g
      rlc_leftPathAvoidGraph gamma' where
  toFun z := rlc_connectorFoldLeft z
  map_rel' := by
    intro x y hxy
    refine ⟨rlc_connectorFoldLeft_adj hxy,
      rlc_connectorFoldLeft_mem_rect gamma gamma' x.2,
      rlc_connectorFoldLeft_mem_rect gamma gamma' y.2,
      rlc_connectorFoldLeft_not_path gamma gamma' x.2,
      rlc_connectorFoldLeft_not_path gamma gamma' y.2⟩



theorem RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictTopSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
    (hz0 : 0 ≤ z 0) : z ∈ rlc_strictTopSet gamma := by
  have hzSet : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hzSet
  have hfold := hreach.map (rlc_connectorFoldRightHom gamma gamma')
  have hfoldOrigin : rlc_connectorFoldRight (origin 2) = origin 2 := by
    ext i
    fin_cases i <;> simp [rlc_connectorFoldRight, origin]
  have hfoldZ : rlc_connectorFoldRight z = z := by
    simp [rlc_connectorFoldRight, hz0]
  have horiginZ : (rlc_rightPathAvoidGraph gamma).Reachable
      (origin 2) z := by
    change (rlc_rightPathAvoidGraph gamma).Reachable
      (rlc_connectorFoldRight (origin 2))
      (rlc_connectorFoldRight z) at hfold
    rwa [hfoldOrigin, hfoldZ] at hfold
  obtain ⟨top, htop, htopNot, htopOrigin⟩ :=
    hfaith.origin_mem_strictTopSet
  exact ⟨top, htop, htopNot, htopOrigin.trans horiginZ⟩



theorem RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictBottomSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
    (hz0 : z 0 ≤ 0) : z ∈ rlc_strictBottomSet gamma' := by
  have hzSet : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hzSet
  have hfold := hreach.map (rlc_connectorFoldLeftHom gamma gamma')
  have hfoldOrigin : rlc_connectorFoldLeft (origin 2) = origin 2 := by
    ext i
    fin_cases i <;> simp [rlc_connectorFoldLeft, origin]
  have hfoldZ : rlc_connectorFoldLeft z = z := by
    simp [rlc_connectorFoldLeft, hz0]
  have horiginZ : (rlc_leftPathAvoidGraph gamma').Reachable
      (origin 2) z := by
    change (rlc_leftPathAvoidGraph gamma').Reachable
      (rlc_connectorFoldLeft (origin 2))
      (rlc_connectorFoldLeft z) at hfold
    rwa [hfoldOrigin, hfoldZ] at hfold
  obtain ⟨bottom, hbottom, hbottomNot, hbottomOrigin⟩ :=
    hfaith.origin_mem_strictBottomSet
  exact ⟨bottom, hbottom, hbottomNot, hbottomOrigin.trans horiginZ⟩




theorem RlcBookFaithfulTracePair.extremalPairCandidateEdges_disjoint_connectorEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' heCandidate
  have hconnector := (Finset.mem_filter.mp heConnector).2
  obtain ⟨z, hzRegion, hzEdge⟩ := hconnector
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Finset.mem_union] at hexplored
      rw [Sym2.mem_iff] at hzEdge
      rcases hexplored with hright | hleft
      · rw [mem_edgesWithinFinset] at hright
        obtain ⟨u, hu, v, hv, huv⟩ := hright
        have hends : x ∈ rlc_rightExploredVertices gamma ∧
            y ∈ rlc_rightExploredVertices gamma := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [rlc_rightExploredVertices, Finset.mem_sdiff,
          rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictTopVertices]
            exact hfaith.connectorOriginRegion_mem_strictTopSet
              (z := x) hzRegion hx.1.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictTopVertices]
            exact hfaith.connectorOriginRegion_mem_strictTopSet
              (z := y) hzRegion hy.1.1)
      · rw [mem_edgesWithinFinset] at hleft
        obtain ⟨u, hu, v, hv, huv⟩ := hleft
        have hends : x ∈ rlc_leftExploredVertices gamma' ∧
            y ∈ rlc_leftExploredVertices gamma' := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [rlc_leftExploredVertices, Finset.mem_sdiff,
          rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact hfaith.connectorOriginRegion_mem_strictBottomSet
              (z := x) hzRegion hx.1.2.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact hfaith.connectorOriginRegion_mem_strictBottomSet
              (z := y) hzRegion hy.1.2.1)





structure RlcBookFaithfulStratumReplacement {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n) : Prop where
  faithful : RlcBookFaithfulTracePair delta delta'
  right_edges : rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1
  left_edges : rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1
  right_explored : rlc_rightExploredVertices delta =
    rlc_rightExploredVertices gamma
  left_explored : rlc_leftExploredVertices delta' =
    rlc_leftExploredVertices gamma'



theorem rlc_rightExploredVertices_subset_of_pathVertices_subset
    {n : Int} {gamma delta : RlcRightDiagonalPath n}
    (hverts : rlc_pathVertices delta.1 ⊆
      rlc_pathVertices gamma.1) :
    rlc_rightExploredVertices delta ⊆
      rlc_rightExploredVertices gamma := by
  have hdisj : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hzTop hzDelta
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hzTop (hverts hzDelta)
  have htop : rlc_strictTopSet gamma ⊆ rlc_strictTopSet delta :=
    rlc_strictTopSet_mono_of_disjoint_path gamma delta hdisj
  intro z hz
  rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hz ⊢
  exact ⟨hz.1, fun hzTop => hz.2 (by
    rw [rlc_mem_strictTopVertices] at hzTop ⊢
    exact htop hzTop)⟩



theorem rlc_leftExploredVertices_subset_of_pathVertices_subset
    {n : Int} {gamma delta : RlcLeftDiagonalPath n}
    (hverts : rlc_pathVertices delta.1 ⊆
      rlc_pathVertices gamma.1) :
    rlc_leftExploredVertices delta ⊆
      rlc_leftExploredVertices gamma := by
  have hdisj : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hzBottom hzDelta
    exact (Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path gamma)) hzBottom (hverts hzDelta)
  have hbottom : rlc_strictBottomSet gamma ⊆
      rlc_strictBottomSet delta :=
    rlc_strictBottomSet_mono_of_disjoint_path gamma delta hdisj
  intro z hz
  rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hz ⊢
  exact ⟨hz.1, fun hzBottom => hz.2 (by
    rw [rlc_mem_strictBottomVertices] at hzBottom ⊢
    exact hbottom hzBottom)⟩



theorem rlc_rightLowestCandidate_explored_eq_of_open_subset
    {n : Int} {gamma delta : RlcRightDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1)
    (hsub : rlc_rightExploredVertices delta ⊆
      rlc_rightExploredVertices gamma) :
    rlc_rightExploredVertices delta =
      rlc_rightExploredVertices gamma := by
  by_contra hne
  have hstrict : rlc_rightExploredVertices delta ⊂
      rlc_rightExploredVertices gamma :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  exact (rlc_rightLowestCandidate_not_open_of_below hgamma
    (Or.inl hstrict)) hdelta



theorem rlc_leftHighestCandidate_explored_eq_of_open_subset
    {n : Int} {gamma delta : RlcLeftDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1)
    (hsub : rlc_leftExploredVertices delta ⊆
      rlc_leftExploredVertices gamma) :
    rlc_leftExploredVertices delta =
      rlc_leftExploredVertices gamma := by
  by_contra hne
  have hstrict : rlc_leftExploredVertices delta ⊂
      rlc_leftExploredVertices gamma :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  exact (rlc_leftHighestCandidate_not_open_of_above hgamma
    (Or.inl hstrict)) hdelta




theorem RlcBookFaithfulStratumReplacement.of_subpaths
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair delta delta')
    (hrEdges : rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1)
    (hlEdges : rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1)
    (hrVerts : rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1)
    (hlVerts : rlc_pathVertices delta'.1 ⊆ rlc_pathVertices gamma'.1)
    (hactive : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    RlcBookFaithfulStratumReplacement gamma gamma' delta delta' := by
  obtain ⟨omega, hright, hleft⟩ := hactive
  have hopen := rlc_extremalPairCandidate_subset_pathPairOpen
    (gamma, gamma') ⟨hright, hleft⟩
  have hdelta : omega ∈ rlc_pathOpen delta.1 := fun e he =>
    hopen.1 e (hrEdges he)
  have hdelta' : omega ∈ rlc_pathOpen delta'.1 := fun e he =>
    hopen.2 e (hlEdges he)
  exact {
    faithful := hfaith
    right_edges := hrEdges
    left_edges := hlEdges
    right_explored := rlc_rightLowestCandidate_explored_eq_of_open_subset
      hright hdelta
        (rlc_rightExploredVertices_subset_of_pathVertices_subset hrVerts)
    left_explored := rlc_leftHighestCandidate_explored_eq_of_open_subset
      hleft hdelta'
        (rlc_leftExploredVertices_subset_of_pathVertices_subset hlVerts) }



theorem RlcBookFaithfulStratumReplacement.extremalPairCandidateEdges_disjoint_connectorEdges
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta') :
    Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges delta delta') := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' heCandidate
  have hconnector := (Finset.mem_filter.mp heConnector).2
  obtain ⟨z, hzRegion, hzEdge⟩ := hconnector
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Finset.mem_union] at hexplored
      rw [Sym2.mem_iff] at hzEdge
      rcases hexplored with hright | hleft
      · rw [mem_edgesWithinFinset] at hright
        obtain ⟨u, hu, v, hv, huv⟩ := hright
        have hends : x ∈ rlc_rightExploredVertices gamma ∧
            y ∈ rlc_rightExploredVertices gamma := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [← R.right_explored, rlc_rightExploredVertices,
          Finset.mem_sdiff, rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictTopVertices]
            exact R.faithful.connectorOriginRegion_mem_strictTopSet
              (z := x) hzRegion hx.1.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictTopVertices]
            exact R.faithful.connectorOriginRegion_mem_strictTopSet
              (z := y) hzRegion hy.1.1)
      · rw [mem_edgesWithinFinset] at hleft
        obtain ⟨u, hu, v, hv, huv⟩ := hleft
        have hends : x ∈ rlc_leftExploredVertices gamma' ∧
            y ∈ rlc_leftExploredVertices gamma' := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [← R.left_explored, rlc_leftExploredVertices,
          Finset.mem_sdiff, rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact R.faithful.connectorOriginRegion_mem_strictBottomSet
              (z := x) hzRegion hx.1.2.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact R.faithful.connectorOriginRegion_mem_strictBottomSet
              (z := y) hzRegion hy.1.2.1)


theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidateEdges_disjoint_connector
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset :=
  rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient
    gamma gamma'
      hfaith.extremalPairCandidateEdges_disjoint_connectorEdges



theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidateEdges_disjoint_connector
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta') :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph delta delta').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have heCandidate' : e.map Subtype.val ∈
      rlc_extremalPairCandidateEdges (gamma, gamma') :=
    (Finset.mem_filter.mp heCandidate).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heConnector
      exact (Finset.disjoint_left.mp
        R.extremalPairCandidateEdges_disjoint_connectorEdges)
          (by simpa [Sym2.map_mk] using heCandidate') heConnector.2




theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_trace_open
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    ∀ e ∈ (rlc_connectorTraceWiring delta delta').edgeFinset,
      psi e = true := by
  intro e he
  have hselected : rlc_connectorExtendConfig psi ∈
      rlc_extremalPairCandidate (gamma, gamma') := hpsi
  have hopen := rlc_extremalPairCandidate_subset_pathPairOpen
    (gamma, gamma') hselected
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      rcases Finset.mem_union.mp he.2 with hright | hleft
      · have hopenEdge := hopen.1 s((x : Site 2), (y : Site 2))
          (R.right_edges hright)
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using hopenEdge
      · have hopenEdge := hopen.2 s((x : Site 2), (y : Site 2))
          (R.left_edges hleft)
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using hopenEdge



theorem RlcBookFaithfulStratumReplacement.compatibleExteriorFibre
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    RlcConnectorCompatibleExteriorFibre delta delta' H psi where
  connector_le := hGH
  trace_le := hTH
  trace_open := R.finiteExtremalPairCandidate_trace_open hpsi



theorem rlc_finiteExtremalPairCandidate_compatibleExteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    RlcConnectorCompatibleExteriorFibre gamma gamma' H psi where
  connector_le := hGH
  trace_le := hTH
  trace_open := rlc_finiteExtremalPairCandidate_trace_open
    gamma gamma' hpsi



theorem RlcSequentialExtremalExplorationState.toCompatibleExteriorFibre
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H) :
    RlcConnectorCompatibleExteriorFibre gamma gamma' H
      (rlc_connectorRestrictConfig S.rawConfig) where
  connector_le := hGH
  trace_le := hTH
  trace_open := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset] at he
        change S.rawConfig s((x : Site 2), (y : Site 2)) = true
        rcases Finset.mem_union.mp he.2 with hright | hleft
        · exact S.rightTrace_open hright
        · exact S.leftTrace_open hleft



theorem RlcConnectorCompatibleExteriorFibre.trace_le_frozenExterior
    {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorTraceWiring gamma gamma' ≤
      rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
  intro x y hxy
  left
  refine ⟨F.trace_le hxy, ?_, F.trace_open s(x, y) ?_⟩
  · intro hG
    exact rlc_connectorFiniteGraph_adj_not_traceWiring
      gamma gamma' hG hxy
  · rw [SimpleGraph.mem_edgeFinset]
    exact hxy




theorem RlcConnectorCompatibleExteriorFibre.separate_le_inducedWiring
    {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorSeparateWiring gamma gamma' ≤
      rlc_connectorExteriorInducedWiring gamma gamma' H B psi := by
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



noncomputable def rlc_connectorExteriorFibreConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun e =>
  if h : e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeSet
    then eta ⟨e, h⟩ else psi e

theorem rlc_connectorExteriorFibreConfig_agreesOff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.AgreesOff (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
      (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) := by
  intro e he
  have hnot : e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
    intro hmem
    exact he (SimpleGraph.mem_edgeFinset.mpr hmem)
  simp [rlc_connectorExteriorFibreConfig, hnot]

@[simp] theorem rlc_connectorExteriorFibreConfig_restrictActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = eta := by
  funext e
  simp [FK.restrictActive, rlc_connectorExteriorFibreConfig, e.2]

theorem rlc_connectorExteriorFibreConfig_restrictActive_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hrho : FK.AgreesOff
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho) :
    rlc_connectorExteriorFibreConfig gamma gamma' psi
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) =
      rho := by
  funext e
  by_cases he : e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeSet
  · simp [rlc_connectorExteriorFibreConfig, FK.restrictActive, he]
  · rw [rlc_connectorExteriorFibreConfig, dif_neg he]
    exact (hrho e (by
      simpa [SimpleGraph.mem_edgeFinset] using he)).symm



noncomputable def rlc_connectorExteriorFibreEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∈ FK.condFibre
          (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi} where
  toFun eta := ⟨rlc_connectorExteriorFibreConfig gamma gamma' psi eta, by
    rw [FK.mem_condFibre]
    exact rlc_connectorExteriorFibreConfig_agreesOff
      gamma gamma' psi eta⟩
  invFun rho := FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho.1
  left_inv eta :=
    rlc_connectorExteriorFibreConfig_restrictActive gamma gamma' psi eta
  right_inv rho := by
    apply Subtype.ext
    exact rlc_connectorExteriorFibreConfig_restrictActive_eq
      gamma gamma' psi rho.1 (FK.mem_condFibre.mp rho.2)



theorem rlc_openSub_exteriorFibre_sup_frozen {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.openSub H (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) ⊔ B =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma')
          (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) ⊔
        rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hH, hopen⟩ | hB)
    · by_cases hG : (rlc_connectorFiniteGraph gamma gamma').Adj x y
      · left
        refine ⟨hG, ?_⟩
        have he : s(x, y) ∈
            (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hG
        rw [FK.extendActive_apply
          (rlc_connectorFiniteGraph gamma gamma') eta ⟨s(x, y), he⟩]
        simpa [rlc_connectorExteriorFibreConfig, he] using hopen
      · right
        exact Or.inl ⟨hH, hG, by
          simpa [rlc_connectorExteriorFibreConfig,
            show s(x, y) ∉
              (rlc_connectorFiniteGraph gamma gamma').edgeSet by
                rwa [SimpleGraph.mem_edgeSet]] using hopen⟩
    · exact Or.inr (Or.inr hB)
  · rintro (⟨hG, hopen⟩ | (hExt | hB))
    · left
      refine ⟨hGH hG, ?_⟩
      have he : s(x, y) ∈
          (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hG
      rw [rlc_connectorExteriorFibreConfig, dif_pos he]
      rw [FK.extendActive_apply
        (rlc_connectorFiniteGraph gamma gamma') eta ⟨s(x, y), he⟩] at hopen
      exact hopen
    · left
      refine ⟨hExt.1, ?_⟩
      have he : s(x, y) ∉
          (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
        exact hExt.2.1
      simpa [rlc_connectorExteriorFibreConfig, he] using hExt.2.2
    · exact Or.inr hB

private theorem rlc_reachable_of_adj_reachable
    {V : Type*} {A K : SimpleGraph V}
    (hstep : ∀ {x y}, A.Adj x y → K.Reachable x y)
    {x y : V} (hxy : A.Reachable x y) : K.Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact .refl _
  | cons huv w ih => exact (hstep huv).trans ih



theorem rlc_sup_frozen_reachable_iff_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (A : SimpleGraph (RlcConnectorVertex n)) (x y : RlcConnectorVertex n) :
    (A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Reachable x y ↔
      (A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi).Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hA | hE
    · exact Or.inl hA
    · exact Or.inr ⟨hE.ne, hE.reachable⟩
  · intro hxy
    apply rlc_reachable_of_adj_reachable (A :=
      A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi) ?_ hxy
    intro u v huv
    rcases huv with hA | hC
    · exact (show (A ⊔
        rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Adj u v
        from Or.inl hA).reachable
    · exact hC.2.mono le_sup_right



noncomputable def rlc_connectorExteriorComponentEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (A : SimpleGraph (RlcConnectorVertex n)) :
    (A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).ConnectedComponent ≃
      (A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi).ConnectedComponent := by
  let K := A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi
  let L := A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi
  apply Equiv.ofBijective (fun C : K.ConnectedComponent =>
    L.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hL : L.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hK : K.Reachable C.out D.out :=
      (rlc_sup_frozen_reachable_iff_induced
        gamma gamma' H B psi A C.out D.out).mpr hL
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hK
  · intro D
    let C := K.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hK : K.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (rlc_sup_frozen_reachable_iff_induced
      gamma gamma' H B psi A C.out D.out).mp hK



theorem rlc_numClustersBC_exteriorFibre_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.numClustersBC H B
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
  unfold FK.numClustersBC
  rw [rlc_openSub_exteriorFibre_sup_frozen gamma gamma' H B hGH psi eta]
  exact Nat.card_congr (rlc_connectorExteriorComponentEquiv
    gamma gamma' H B psi
      (FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta)))



noncomputable def rlc_connectorExteriorEdgeFactor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) : Real :=
  ∏ e ∈ H.edgeFinset \ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
    if psi e then p else 1 - p



theorem rlc_edgeProduct_exteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) [DecidableRel H.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.edgeProduct H p
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p
          (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
  classical
  let O := H.edgeFinset \
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  have hfactor : rlc_connectorExteriorEdgeFactor gamma gamma' H psi p =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    unfold rlc_connectorExteriorEdgeFactor
    apply Finset.prod_congr
    · ext e
      simp [O]
    · intro e he
      rfl
  have hsub : (rlc_connectorFiniteGraph gamma gamma').edgeFinset ⊆
      H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact hGH he
  have hedges : H.edgeFinset =
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset ∪ O := by
    exact (Finset.union_sdiff_of_subset hsub).symm
  have hdisj : Disjoint
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset O :=
    Finset.disjoint_sdiff
  have hinner :
      (∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
        if rlc_connectorExteriorFibreConfig gamma gamma' psi eta e
          then p else 1 - p) =
      ∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
        if FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta e
          then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heSet : e ∈
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      rwa [← SimpleGraph.mem_edgeFinset]
    have hfibre : rlc_connectorExteriorFibreConfig
        gamma gamma' psi eta e = eta ⟨e, heSet⟩ := by
      simp [rlc_connectorExteriorFibreConfig, heSet]
    have hactive := FK.extendActive_apply
      (rlc_connectorFiniteGraph gamma gamma') eta ⟨e, heSet⟩
    rw [hfibre, hactive]
  have houter :
      (∏ e ∈ O,
        if rlc_connectorExteriorFibreConfig gamma gamma' psi eta e
          then p else 1 - p) =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heNot : e ∉
        (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
      have : e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeFinset :=
        (Finset.mem_sdiff.mp he).2
      simpa [SimpleGraph.mem_edgeFinset] using this
    have hfibre : rlc_connectorExteriorFibreConfig
        gamma gamma' psi eta e = psi e := by
      simp [rlc_connectorExteriorFibreConfig, heNot]
    rw [hfibre]
  unfold FK.edgeProduct
  rw [hedges, Finset.prod_union hdisj, hinner, houter, hfactor]
  exact mul_comm
    (∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
      if FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta e
        then p else 1 - p)
    (∏ e ∈ O, if psi e then p else 1 - p)



theorem rlc_bcWeight_exteriorFibre_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.bcWeight H B p q
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by
  rw [FK.bcWeight,
    rlc_edgeProduct_exteriorFibre gamma gamma' H hGH psi p eta,
    rlc_numClustersBC_exteriorFibre_eq_induced
      gamma gamma' H B hGH psi eta]
  rw [FK.activeBCWeight_const_eq_bcWeight]
  unfold FK.bcWeight
  ring

set_option maxHeartbeats 800000 in



theorem rlc_connectorExteriorFibre_inducedBcZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) :
    FK.inducedBcZ H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi =
      rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q := by
  unfold FK.inducedBcZ FK.activeBCZ
  let S := FK.condFibre
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
  let weight := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    FK.bcWeight H B p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((rlc_connectorExteriorFibreEquiv
        gamma gamma' psi) eta) :=
      (Equiv.sum_comp (rlc_connectorExteriorFibreEquiv gamma gamma' psi)
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact rlc_bcWeight_exteriorFibre_eq_induced
        gamma gamma' H B hGH psi p q eta
    _ = rlc_connectorExteriorEdgeFactor gamma gamma' H psi p *
        ∑ eta, FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
          (fun _ => p) q eta := by rw [Finset.mul_sum]




theorem rlc_connectorExteriorFibre_condBcProb_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
      FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (fun _ => p) q eta := by
  unfold FK.condBcProb FK.activeBCProb
  rw [if_pos (rlc_connectorExteriorFibreConfig_agreesOff
    gamma gamma' psi eta)]
  rw [rlc_bcWeight_exteriorFibre_eq_induced
      gamma gamma' H B hGH psi p q eta,
    rlc_connectorExteriorFibre_inducedBcZ_eq
      gamma gamma' H B hGH psi p q]
  exact mul_div_mul_left _ _ (by
    unfold rlc_connectorExteriorEdgeFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    split
    · exact hp.ne'
    · exact (sub_pos.mpr hp1).ne')


noncomputable def rlc_connectorExteriorFibreCondEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) : Real :=
  ∑ eta,
    (rlc_connectorActiveEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
      FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
        (rlc_connectorExteriorFibreConfig gamma gamma' psi eta)


theorem rlc_connectorExteriorFibreCondEventMass_eq_activeInduced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (fun _ => p) q (rlc_connectorActiveEvent gamma gamma') := by
  classical
  unfold rlc_connectorExteriorFibreCondEventMass FK.activeBCProbOf
    FK.activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorExteriorFibre_condBcProb_eq_induced
    gamma gamma' H B hGH psi hp hp1 eta]



theorem rlc_connectorExteriorFibreCondEventMass_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  classical
  rw [rlc_connectorExteriorFibreCondEventMass_eq_activeInduced
      gamma gamma' H B hGH psi hp hp1,
    FK.activeBCProbOf_eq_bcProb_preimage
      (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
      hp hp1 hq,
    rlc_connectorActiveEvent_preimage]
  rfl

set_option maxHeartbeats 800000 in




theorem rlc_connectorExteriorFibreCondEventMass_eq_ambientSum {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      ∑ rho,
        (rlc_finiteConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho := by
  classical
  let S := FK.condFibre
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
  let term := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    (rlc_finiteConnectorEvent gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho
  have hrestrict : (∑ rho, term rho) = ∑ rho ∈ S, term rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    have hnot : ¬ FK.AgreesOff
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho := by
      rw [FK.mem_condFibre] at hrho
      exact hrho
    unfold term FK.condBcProb
    rw [if_neg hnot, mul_zero]
  symm
  calc
    (∑ rho, term rho) = ∑ rho ∈ S, term rho := hrestrict
    _ = ∑ rho : {rho // rho ∈ S}, term rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) term
    _ = ∑ eta, term ((rlc_connectorExteriorFibreEquiv
        gamma gamma' psi) eta) :=
      (Equiv.sum_comp (rlc_connectorExteriorFibreEquiv gamma gamma' psi)
        (fun rho => term rho.1)).symm
    _ = rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q := by
      unfold rlc_connectorExteriorFibreCondEventMass term
      apply Finset.sum_congr rfl
      intro eta _
      change
        (rlc_finiteConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real))
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
        (rlc_connectorActiveEvent gamma gamma').indicator
            (fun _ => (1 : Real)) eta *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta)
      have hevent :
          rlc_connectorExteriorFibreConfig gamma gamma' psi eta ∈
              rlc_finiteConnectorEvent gamma gamma' ↔
            eta ∈ rlc_connectorActiveEvent gamma gamma' := by
        rw [← rlc_connectorActiveEvent_preimage]
        simp only [Set.mem_preimage,
          rlc_connectorExteriorFibreConfig_restrictActive]
      by_cases heta : eta ∈ rlc_connectorActiveEvent gamma gamma'
      · rw [Set.indicator_of_mem heta,
          Set.indicator_of_mem (hevent.mpr heta)]
      · simp only [Set.indicator_of_notMem heta,
          Set.indicator_of_notMem (fun h => heta (hevent.mp h)),
          zero_mul]



theorem rlc_connectorExteriorFibreCondEventMass_ge_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') ≤
      rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi
        (BeffaraDC.selfDualPoint q) q := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [rlc_connectorExteriorFibreCondEventMass_eq_induced
    gamma gamma' H B F.connector_le psi hp hp1 hq0]
  exact FK.bcProb_mono_bc
    (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
    (F.separate_le_inducedWiring B) hp hp1 hq
    (rlc_finiteConnectorEvent_isIncreasing gamma gamma')



theorem RlcSequentialExtremalExplorationState.connectorConditionalMass_ge_separate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') ≤
      rlc_connectorExteriorFibreCondEventMass gamma gamma' H B
        (rlc_connectorRestrictConfig S.rawConfig)
        (BeffaraDC.selfDualPoint q) q :=
  rlc_connectorExteriorFibreCondEventMass_ge_separate
    gamma gamma' H B (rlc_connectorRestrictConfig S.rawConfig)
      (S.toCompatibleExteriorFibre H hGH hTH) hq




theorem rlc_connectorOutsideEventMass_lower {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    (hS : FK.DependsOnOutside
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset S)
    (hcompat : ∀ {psi}, psi ∈ S →
      RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩ S).indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let F := (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  let A := rlc_finiteConnectorEvent gamma gamma'
  let alpha := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q A
  change alpha *
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
  · have hres := rlc_connectorExteriorFibreCondEventMass_ge_separate
      gamma gamma' H B psi (hcompat hpsiS) hq
    rw [rlc_connectorExteriorFibreCondEventMass_eq_ambientSum
      gamma gamma' H B psi (BeffaraDC.selfDualPoint q) q] at hres
    change alpha ≤
      ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho at hres
    rw [Set.indicator_of_mem hpsiS]
    simp only [mul_one, one_mul]
    change alpha * mass ≤ mass *
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho)
    calc
      alpha * mass = mass * alpha := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hres hmass
  · simp [Set.indicator_of_notMem hpsiS]




theorem rlc_finiteExtremalPairCandidate_connectorMass_lower {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let F := (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  let A := rlc_finiteConnectorEvent gamma gamma'
  let S := rlc_finiteExtremalPairCandidate gamma gamma'
  let alpha := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q A
  have hS : FK.DependsOnOutside F S := by
    exact rlc_finiteExtremalPairCandidate_dependsOnOutside
      gamma gamma' hdisj
  change alpha *
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
  · have hcompat : RlcConnectorCompatibleExteriorFibre
        gamma gamma' H psi := by
      apply rlc_finiteExtremalPairCandidate_compatibleExteriorFibre
        gamma gamma' H hGH hTH
      exact hpsiS
    have hres := rlc_connectorExteriorFibreCondEventMass_ge_separate
      gamma gamma' H B psi hcompat hq
    rw [rlc_connectorExteriorFibreCondEventMass_eq_ambientSum
      gamma gamma' H B psi (BeffaraDC.selfDualPoint q) q] at hres
    change alpha ≤
      ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho at hres
    rw [Set.indicator_of_mem hpsiS]
    simp only [mul_one, one_mul]
    change alpha * mass ≤ mass *
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho)
    calc
      alpha * mass = mass * alpha := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hres hmass
  · simp [Set.indicator_of_notMem hpsiS]




theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_lower
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
        (rlc_connectorSeparateWiring delta delta')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent delta delta') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent delta delta') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  apply rlc_connectorOutsideEventMass_lower delta delta' H B
    (rlc_finiteExtremalPairCandidate gamma gamma')
  · intro psi rho hagree
    apply indic_iff
    apply rlc_finiteExtremalPairCandidate_dependsOn
    intro e he
    exact (hagree e (fun heG =>
      (Finset.disjoint_left.mp
        R.finiteExtremalPairCandidateEdges_disjoint_connector) he heG)).symm
  · intro psi hpsi
    exact R.compatibleExteriorFibre H hGH hTH hpsi
  · exact hq



theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_selfDual_ge
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {q : Real} (hq : 1 ≤ q)
    (hdual :
      rlc_connectorForcedDualEventMass delta delta'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent delta delta')ᶜ ≤
        FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
          (rlc_connectorMergedWiring delta delta')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent delta delta')) :
    1 / (1 + q) *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent delta delta') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let stratumMass := ∑ rho,
    (rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  have hmass : 0 ≤ stratumMass := Finset.sum_nonneg fun rho _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)
      (FK.bcProb_nonneg H B hp hp1 hq0 rho)
  have hfloor := rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    delta delta' hq hdual
  have haggregate :=
    R.finiteExtremalPairCandidate_connectorMass_lower H B hGH hTH hq
  change 1 / (1 + q) * stratumMass ≤ _
  calc
    1 / (1 + q) * stratumMass ≤
        FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
            (rlc_connectorSeparateWiring delta delta')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent delta delta') * stratumMass :=
      mul_le_mul_of_nonneg_right hfloor hmass
    _ ≤ _ := haggregate





theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_lower
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho :=
  rlc_finiteExtremalPairCandidate_connectorMass_lower
    gamma gamma' H B hGH hTH
      hfaith.finiteExtremalPairCandidateEdges_disjoint_connector hq




theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_selfDual_ge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ ≤
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let stratumMass := ∑ rho,
    (rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  have hmass : 0 ≤ stratumMass := Finset.sum_nonneg fun rho _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)
      (FK.bcProb_nonneg H B hp hp1 hq0 rho)
  have hfloor := rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq hdual
  have haggregate :=
    hfaith.finiteExtremalPairCandidate_connectorMass_lower
      H B hGH hTH hq
  change 1 / (1 + q) * stratumMass ≤ _
  calc
    1 / (1 + q) * stratumMass ≤
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma') * stratumMass :=
      mul_le_mul_of_nonneg_right hfloor hmass
    _ ≤ _ := haggregate

end

end StatMech.Universality
