/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelVisibleFibreHall










open Finset SimpleGraph Set

namespace StatMech.Universality

noncomputable section



noncomputable def rlc_twoChannelPIMSFixedEquivDiscarded {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    RlcTwoChannelPIMSFixedTargetEdge gamma gamma' ≃
      RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' where
  toFun e := ⟨rlc_twoChannelPIMSEdgePerm gamma gamma' e.1, by
    rintro ⟨v, hv⟩
    apply e.2
    have heq : e.1 = v.1 := by
      apply (rlc_twoChannelPIMSEdgePerm gamma gamma').injective
      rw [rlc_twoChannelPIMSEdgePerm_variable]
      exact hv.symm
    rw [heq]
    exact v.2⟩
  invFun e := ⟨(rlc_twoChannelPIMSEdgePerm gamma gamma').symm e.1, by
    intro hcentral
    let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨(rlc_twoChannelPIMSEdgePerm gamma gamma').symm e.1, hcentral⟩
    apply e.2
    refine ⟨v, ?_⟩
    rw [← rlc_twoChannelPIMSEdgePerm_variable v]
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').apply_symm_apply e.1⟩
  left_inv e := by
    apply Subtype.ext
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').symm_apply_apply e.1
  right_inv e := by
    apply Subtype.ext
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').apply_symm_apply e.1



def rlc_twoChannelConfigOfVisibleFixed {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma')) :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  fun e => if hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma' then
    base ⟨e, hvariable⟩
  else
    bits ⟨e, hvariable⟩

@[simp] theorem rlc_twoChannelConfigOfVisibleFixed_variable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma'))
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed base bits e.1 = base e := by
  simp [rlc_twoChannelConfigOfVisibleFixed, e.2]

@[simp] theorem rlc_twoChannelConfigOfVisibleFixed_fixed {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma'))
    (e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed base bits e.1 = bits e := by
  simp [rlc_twoChannelConfigOfVisibleFixed, e.2]


abbrev RlcTwoChannelSuccessFixedPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :=
  {bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') //
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelConfigOfVisibleFixed base bits) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'}



def rlc_twoChannelSuccessVisibleFibreEquivFixedPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelSuccessVisibleFibre base ≃
      RlcTwoChannelSuccessFixedPayload base where
  toFun eta := ⟨fun e => eta.1.1 e.1, by
    have hconfig : rlc_twoChannelConfigOfVisibleFixed base
        (fun e => eta.1.1 e.1) = eta.1.1 := by
      funext e
      by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        have hbase := congrFun eta.2 v
        simpa [rlc_twoChannelConfigOfVisibleFixed, hvariable,
          rlc_twoChannelSuccessVisibleBase] using hbase.symm
      · simp [rlc_twoChannelConfigOfVisibleFixed, hvariable]
    rw [hconfig]
    exact eta.1.2⟩
  invFun bits :=
    ⟨⟨rlc_twoChannelConfigOfVisibleFixed base bits.1, bits.2⟩, by
      funext e
      exact rlc_twoChannelConfigOfVisibleFixed_variable base bits.1 e⟩
  left_inv eta := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
        rlc_connectorCentralFaceEdges gamma gamma'
    · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
        ⟨e, hvariable⟩
      have hbase := congrFun eta.2 v
      simpa [rlc_twoChannelConfigOfVisibleFixed, hvariable,
        rlc_twoChannelSuccessVisibleBase] using hbase.symm
    · simp [rlc_twoChannelConfigOfVisibleFixed, hvariable]
  right_inv bits := by
    apply Subtype.ext
    funext e
    exact rlc_twoChannelConfigOfVisibleFixed_fixed base bits.1 e




def rlc_twoChannelFailureVisibleFibreDiscardedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      ConfigSpace (RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma') where
  toFun rho e := rho.1.1 e.1
  inj' := by
    intro rho sigma hbits
    apply Subtype.ext
    apply Subtype.ext
    apply
      rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    apply Prod.ext
    · funext e
      by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        have hrho := congrFun rho.2 v
        have hsigma := congrFun sigma.2 v
        change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho.1).1 v.1 =
          base v at hrho
        change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma.1).1 v.1 =
          base v at hsigma
        rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val] at hrho hsigma
        exact hrho.trans hsigma.symm
      · let f : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        exact rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq
          rho.1.1 sigma.1.1 f
    · funext e
      exact congrFun hbits e



def rlc_twoChannelFailureComplementFixedBits {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :=
  fun e => !(rho.1 (rlc_twoChannelPIMSFixedEquivDiscarded e).1)



theorem rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) =
      rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 := by
  funext e
  by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma'
  · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    rw [show rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) e =
      rlc_twoChannelFailureVisibleBase hclosure rho v by
        exact rlc_twoChannelConfigOfVisibleFixed_variable _ _ v]
    change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 v.1 = _
    rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
    exact (rlc_twoChannelFullPIMSConfig_variable_eq_projection rho.1 v).symm
  · let f : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' := ⟨e, hvariable⟩
    rw [show rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) e =
      rlc_twoChannelFailureComplementFixedBits rho f by
        exact rlc_twoChannelConfigOfVisibleFixed_fixed _ _ f]
    rfl



def rlc_twoChannelFailureComplementFixedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') where
  toFun rho := rlc_twoChannelFailureComplementFixedBits rho.1
  inj' := by
    intro rho sigma hbits
    apply
      (rlc_twoChannelFailureVisibleFibreDiscardedEmbedding base).injective
    funext e
    let f := (rlc_twoChannelPIMSFixedEquivDiscarded
      (gamma := gamma) (gamma' := gamma')).symm e
    have h := congrFun hbits f
    change Bool.not (rho.1.1
        (rlc_twoChannelPIMSFixedEquivDiscarded f).1) =
      Bool.not (sigma.1.1
        (rlc_twoChannelPIMSFixedEquivDiscarded f).1) at h
    have hval : (rlc_twoChannelPIMSFixedEquivDiscarded f).1 = e.1 :=
      congrArg Subtype.val
        ((rlc_twoChannelPIMSFixedEquivDiscarded
          (gamma := gamma) (gamma' := gamma')).apply_symm_apply e)
    rw [hval] at h
    exact Bool.not_injective h





def RlcTwoChannelFullPIMSPhysicalSuccess {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  forall rho : RlcTwoChannelEdgeFailure gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPIMSConfig gamma gamma' rho.1) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'



theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPIMSPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hphysical : RlcTwoChannelFullPIMSPhysicalSuccess gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure := by
  intro base
  apply Fintype.card_le_of_embedding
  exact
    { toFun := fun rho =>
        (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base).symm
          ⟨rlc_twoChannelFailureComplementFixedBits rho.1, by
            have hconfig : rlc_twoChannelConfigOfVisibleFixed base
                (rlc_twoChannelFailureComplementFixedBits rho.1) =
              rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 := by
              calc
                _ = rlc_twoChannelConfigOfVisibleFixed
                    (rlc_twoChannelFailureVisibleBase hclosure rho.1)
                    (rlc_twoChannelFailureComplementFixedBits rho.1) := by
                      rw [rho.2]
                _ = _ :=
                  rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS
                    hclosure rho.1
            rw [hconfig]
            exact hphysical rho.1⟩
      inj' := by
        intro rho sigma h
        have hpayload := congrArg
          (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base) h
        have hbits :
            rlc_twoChannelFailureComplementFixedBits rho.1 =
              rlc_twoChannelFailureComplementFixedBits sigma.1 := by
          simpa using congrArg Subtype.val hpayload
        exact (rlc_twoChannelFailureComplementFixedEmbedding base).injective
          hbits }


theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_fixedPayload
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      forall base : RlcTwoChannelPIMSVisibleBase gamma gamma',
        Fintype.card (RlcTwoChannelFailureVisibleFibre hclosure base) <=
          Fintype.card (RlcTwoChannelSuccessFixedPayload base) := by
  constructor <;> intro h base
  · rw [← Fintype.card_congr
      (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base)]
    exact h base
  · rw [Fintype.card_congr
      (rlc_twoChannelSuccessVisibleFibreEquivFixedPayload base)]
    exact h base

end

end StatMech.Universality
