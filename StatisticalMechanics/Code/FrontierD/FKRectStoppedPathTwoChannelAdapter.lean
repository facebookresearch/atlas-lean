/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalWitnessStep
import Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Code.Universality.RSWSequentialStoppedConditionalLaw










open scoped BigOperators
open SimpleGraph

namespace StatMech.FrontierD

open StatMech StatMech.Lattice
open StatMech.Universality

noncomputable section


theorem FK.configHammingCount_le_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega eta : ConfigSpace (Sym2 V)) :
    FK.configHammingCount G omega eta <= G.edgeFinset.card := by
  let A := FK.diffSet G omega eta
  let B := FK.diffSet G eta omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [A, B, FK.diffSet, Finset.mem_filter] at heA heB
    exact Bool.noConfusion (heA.2.1.symm.trans heB.2.2)
  have hunion : A ∪ B ⊆ G.edgeFinset := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heA | heB
    · exact (Finset.mem_filter.mp heA).1
    · exact (Finset.mem_filter.mp heB).1
  unfold FK.configHammingCount
  change A.card + B.card <= G.edgeFinset.card
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hunion




theorem
    rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma'
      ((rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2) := by
  intro rho
  let source := rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1
  let target := rlc_twoChannelEdgeConfigExtend gamma gamma'
    (rlc_twoChannelFullPhysicalPermConfig gamma gamma' rho.1)
  have hscore := rlc_twoChannel_score_le_hamming_add_two
    gamma gamma' source target
  have hhamming := FK.configHammingCount_le_edgeFinset_card
    (rlc_connectorTwoChannelGraph gamma gamma') source target
  dsimp only [source, target] at hscore hhamming ⊢
  omega





theorem
    rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch
      (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi =
      rlc_connectorSeparateWiring gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      ∑ rho : ConfigSpace (Sym2 Vout),
        (FK.ocd_innerRestrict iota ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q
            (FK.ocd_innerEdgeFinset iota) psi rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp := (BeffaraDC.selfDualPoint_mem_Ioo hq0).1
  have hp1 := (BeffaraDC.selfDualPoint_mem_Ioo hq0).2
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let B : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹' A
  have hdm := FK.ocd_condBcProb_psiExt_sum_eq_inducedBox
    (Gin := rlc_connectorTwoChannelGraph gamma gamma')
    (Gout := Gout) (ιV := iota) (bdryOut := bdryOut)
    hiota hadj hp hp1 hq0 psi B
  have hpre : FK.ocd_psiExt iota psi ⁻¹' B = A := by
    ext omega
    simp only [B, A, Set.mem_preimage,
      FK.ocd_innerRestrict_psiExt hiota]
  rw [hpre] at hdm
  have hdm' :
      (∑ rho : ConfigSpace (Sym2 Vout),
          B.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q
              (FK.ocd_innerEdgeFinset iota) psi rho) =
        ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (rlc_connectorSeparateWiring gamma gamma')
              (BeffaraDC.selfDualPoint q) q omega := by
    calc
      _ = ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (FK.ocd_inducedWiring Gout iota bdryOut psi)
              (BeffaraDC.selfDualPoint q) q omega := hdm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro omega _
        rw [FK.bcProb_congr_boundary
          (rlc_connectorTwoChannelGraph gamma gamma')
          (FK.ocd_inducedWiring Gout iota bdryOut psi)
          (rlc_connectorSeparateWiring gamma gamma') hwire]
  have hlocal :=
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut
      hinc hstatic hq N hscore
  rw [FK.bcEventMass] at hlocal
  exact hlocal.trans_eq hdm'.symm



theorem
    rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch
      (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi =
      rlc_connectorSeparateWiring gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) *
        (∑ sigma ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi,
          FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q sigma) <=
      ∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (FK.bcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q) rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp := (BeffaraDC.selfDualPoint_mem_Ioo hq0).1
  have hp1 := (BeffaraDC.selfDualPoint_mem_Ioo hq0).2
  let F := FK.ocd_innerEdgeFinset iota
  let A : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹'
      rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let M := ∑ sigma ∈ FK.condFibre F psi,
    FK.bcProb Gout (boundaryCliqueGraph bdryOut)
      (BeffaraDC.selfDualPoint q) q sigma
  let C := ∑ rho : ConfigSpace (Sym2 Vout),
    A.indicator (fun _ => (1 : Real)) rho *
      FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
        (BeffaraDC.selfDualPoint q) q F psi rho
  have hcond : 1 / (1 + (Real.sqrt q) ^ N * q) <= C := by
    simpa only [F, A, C] using
      rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut
        hinc hstatic iota hiota hadj psi hwire hq N hscore
  have hM : 0 <= M := by
    exact Finset.sum_nonneg fun sigma _ =>
      FK.bcProb_nonneg Gout (boundaryCliqueGraph bdryOut)
        hp hp1 hq0 sigma
  have hraw := FK.bcProb_event_fibre_eq_mass_mul_cond
    Gout (boundaryCliqueGraph bdryOut) hp hp1 hq0 F psi A
  have hind : forall rho : ConfigSpace (Sym2 Vout),
      A.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q rho =
        A.indicator
          (FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q) rho := by
    intro rho
    by_cases hrho : rho ∈ A <;> simp [hrho]
  change 1 / (1 + (Real.sqrt q) ^ N * q) * M <=
    ∑ rho ∈ FK.condFibre F psi,
      A.indicator
        (FK.bcProb Gout (boundaryCliqueGraph bdryOut)
          (BeffaraDC.selfDualPoint q) q) rho
  calc
    1 / (1 + (Real.sqrt q) ^ N * q) * M <= M * C := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcond hM
    _ = ∑ rho ∈ FK.condFibre F psi,
        A.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q rho := hraw.symm
    _ = ∑ rho ∈ FK.condFibre F psi,
        A.indicator
          (FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q) rho := by
      apply Finset.sum_congr rfl
      intro rho _
      exact hind rho



theorem
    rlc_twoChannel_condBcProb_ge_one_div_one_add_q_sq_of_staticCut
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch
      (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi =
      rlc_connectorSeparateWiring gamma gamma')
    {q : Real} (hq : 1 <= q)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' 2) :
    1 / (1 + q ^ 2) <=
      ∑ rho : ConfigSpace (Sym2 Vout),
        (FK.ocd_innerRestrict iota ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q
            (FK.ocd_innerEdgeFinset iota) psi rho := by
  have h := rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut
    hinc hstatic iota hiota hadj psi hwire hq 2 hscore
  rw [Real.sq_sqrt (by positivity : (0 : Real) <= q)] at h
  simpa [pow_two] using h




theorem
    rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut_edgeCard
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch
      (rlc_connectorTwoChannelGraph gamma gamma') Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (hwire : FK.ocd_inducedWiring Gout iota bdryOut psi =
      rlc_connectorSeparateWiring gamma gamma')
    {q : Real} (hq : 1 <= q) :
    let N := (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card + 2
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      ∑ rho : ConfigSpace (Sym2 Vout),
        (FK.ocd_innerRestrict iota ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q
            (FK.ocd_innerEdgeFinset iota) psi rho := by
  dsimp only
  exact rlc_twoChannel_condBcProb_ge_of_retainedAnchor_staticCut
    hinc hstatic iota hiota hadj psi hwire hq _
      (rlc_twoChannelFullPhysicalPermutationScoreDefect_edgeCard_add_two
        gamma gamma')










theorem rlc_bookFaithfulStoppedPair_condBcProb_outerFibre_lower
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H : SimpleGraph (RlcConnectorVertex n)) [DecidableRel H.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' <= H)
    (hTH : rlc_connectorTraceWiring gamma gamma' <= H)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch H Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring Gout iota bdryOut psi = C)
    {q c : Real} (hq : 1 <= q)
    (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')) :
    c *
        (∑ rho : ConfigSpace (Sym2 Vout),
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q
              (FK.ocd_innerEdgeFinset iota) psi rho) <=
      ∑ rho : ConfigSpace (Sym2 Vout),
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q
            (FK.ocd_innerEdgeFinset iota) psi rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let S := rlc_finiteExtremalPairCandidate gamma gamma'
  let A := rlc_finiteConnectorEvent gamma gamma' ∩ S
  let Sout : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹' S
  let Aout : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹' A
  have hpreS : FK.ocd_psiExt iota psi ⁻¹' Sout = S := by
    ext omega
    simp only [Sout, Set.mem_preimage,
      FK.ocd_innerRestrict_psiExt hiota]
  have hpreA : FK.ocd_psiExt iota psi ⁻¹' Aout = A := by
    ext omega
    simp only [Aout, Set.mem_preimage,
      FK.ocd_innerRestrict_psiExt hiota]
  have hdmS := FK.ocd_condBcProb_psiExt_sum_eq_inducedBox
    (Gin := H) (Gout := Gout) (ιV := iota) (bdryOut := bdryOut)
    hiota hadj hp hp1 hq0 psi Sout
  have hdmA := FK.ocd_condBcProb_psiExt_sum_eq_inducedBox
    (Gin := H) (Gout := Gout) (ιV := iota) (bdryOut := bdryOut)
    hiota hadj hp hp1 hq0 psi Aout
  rw [hpreS] at hdmS
  rw [hpreA] at hdmA
  have hdmS' :
      (∑ rho : ConfigSpace (Sym2 Vout),
          Sout.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q
              (FK.ocd_innerEdgeFinset iota) psi rho) =
        ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          S.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb H C (BeffaraDC.selfDualPoint q) q omega := by
    calc
      _ = ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          S.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb H (FK.ocd_inducedWiring Gout iota bdryOut psi)
              (BeffaraDC.selfDualPoint q) q omega := hdmS
      _ = _ := by
        apply Finset.sum_congr rfl
        intro omega _
        rw [FK.bcProb_congr_boundary H
          (FK.ocd_inducedWiring Gout iota bdryOut psi) C hC]
  have hdmA' :
      (∑ rho : ConfigSpace (Sym2 Vout),
          Aout.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q
              (FK.ocd_innerEdgeFinset iota) psi rho) =
        ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb H C (BeffaraDC.selfDualPoint q) q omega := by
    calc
      _ = ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb H (FK.ocd_inducedWiring Gout iota bdryOut psi)
              (BeffaraDC.selfDualPoint q) q omega := hdmA
      _ = _ := by
        apply Finset.sum_congr rfl
        intro omega _
        rw [FK.bcProb_congr_boundary H
          (FK.ocd_inducedWiring Gout iota bdryOut psi) C hC]
  have hSnonneg :
      0 <= ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb H C (BeffaraDC.selfDualPoint q) q rho := by
    apply Finset.sum_nonneg
    intro rho _
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)
      (FK.bcProb_nonneg H C hp hp1 hq0 rho)
  have haggregate :=
    hfaith.finiteExtremalPairCandidate_connectorMass_lower
      H C hGH hTH hq
  change c *
      (∑ rho : ConfigSpace (Sym2 Vout),
        Sout.indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q
            (FK.ocd_innerEdgeFinset iota) psi rho) <=
    ∑ rho : ConfigSpace (Sym2 Vout),
      Aout.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
          (BeffaraDC.selfDualPoint q) q
          (FK.ocd_innerEdgeFinset iota) psi rho
  rw [hdmS', hdmA']
  calc
    c * (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H C (BeffaraDC.selfDualPoint q) q rho) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma') *
        (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb H C (BeffaraDC.selfDualPoint q) q rho) :=
      mul_le_mul_of_nonneg_right hc hSnonneg
    _ <= ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H C (BeffaraDC.selfDualPoint q) q rho := haggregate




theorem rlc_bookFaithfulStoppedPair_bcProb_outerFibre_lower
    {Vout : Type*} [Fintype Vout] [DecidableEq Vout]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {bdryOut : Vout -> Prop} [DecidablePred bdryOut]
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H : SimpleGraph (RlcConnectorVertex n)) [DecidableRel H.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' <= H)
    (hTH : rlc_connectorTraceWiring gamma gamma' <= H)
    (iota : RlcConnectorVertex n -> Vout)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch H Gout iota)
    (psi : ConfigSpace (Sym2 Vout))
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : FK.ocd_inducedWiring Gout iota bdryOut psi = C)
    {q c : Real} (hq : 1 <= q)
    (hc : c <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')) :
    c *
        (∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi,
          (FK.ocd_innerRestrict iota ⁻¹'
            rlc_finiteExtremalPairCandidate gamma gamma').indicator
              (fun _ => (1 : Real)) rho *
            FK.bcProb Gout (boundaryCliqueGraph bdryOut)
              (BeffaraDC.selfDualPoint q) q rho) <=
      ∑ rho ∈ FK.condFibre (FK.ocd_innerEdgeFinset iota) psi,
        (FK.ocd_innerRestrict iota ⁻¹'
          (rlc_finiteConnectorEvent gamma gamma' ∩
            rlc_finiteExtremalPairCandidate gamma gamma')).indicator
              (fun _ => (1 : Real)) rho *
          FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let F := FK.ocd_innerEdgeFinset iota
  let Sout : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹'
      rlc_finiteExtremalPairCandidate gamma gamma'
  let Aout : Set (ConfigSpace (Sym2 Vout)) :=
    FK.ocd_innerRestrict iota ⁻¹'
      (rlc_finiteConnectorEvent gamma gamma' ∩
        rlc_finiteExtremalPairCandidate gamma gamma')
  let M := ∑ sigma ∈ FK.condFibre F psi,
    FK.bcProb Gout (boundaryCliqueGraph bdryOut)
      (BeffaraDC.selfDualPoint q) q sigma
  let CS := ∑ rho : ConfigSpace (Sym2 Vout),
    Sout.indicator (fun _ => (1 : Real)) rho *
      FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
        (BeffaraDC.selfDualPoint q) q F psi rho
  let CA := ∑ rho : ConfigSpace (Sym2 Vout),
    Aout.indicator (fun _ => (1 : Real)) rho *
      FK.condBcProb Gout (boundaryCliqueGraph bdryOut)
        (BeffaraDC.selfDualPoint q) q F psi rho
  have hcond : c * CS <= CA := by
    simpa only [F, Sout, Aout, CS, CA] using
      rlc_bookFaithfulStoppedPair_condBcProb_outerFibre_lower
        hfaith H hGH hTH iota hiota hadj psi C hC hq hc
  have hM : 0 <= M := Finset.sum_nonneg fun sigma _ =>
    FK.bcProb_nonneg Gout (boundaryCliqueGraph bdryOut)
      hp hp1 hq0 sigma
  have hrawS := FK.bcProb_event_fibre_eq_mass_mul_cond
    Gout (boundaryCliqueGraph bdryOut) hp hp1 hq0 F psi Sout
  have hrawA := FK.bcProb_event_fibre_eq_mass_mul_cond
    Gout (boundaryCliqueGraph bdryOut) hp hp1 hq0 F psi Aout
  change c *
      (∑ rho ∈ FK.condFibre F psi,
        Sout.indicator (fun _ => (1 : Real)) rho *
          FK.bcProb Gout (boundaryCliqueGraph bdryOut)
            (BeffaraDC.selfDualPoint q) q rho) <=
    ∑ rho ∈ FK.condFibre F psi,
      Aout.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb Gout (boundaryCliqueGraph bdryOut)
          (BeffaraDC.selfDualPoint q) q rho
  rw [hrawS, hrawA]
  change c * (M * CS) <= M * CA
  calc
    c * (M * CS) = M * (c * CS) := by ring
    _ <= M * CA := mul_le_mul_of_nonneg_left hcond hM

end

end StatMech.FrontierD
