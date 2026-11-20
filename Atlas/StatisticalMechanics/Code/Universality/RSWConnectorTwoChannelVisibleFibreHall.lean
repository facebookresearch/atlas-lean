/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.ScratchTwoChannelFullDual











open Finset SimpleGraph Set

namespace StatMech.Universality

noncomputable section


abbrev RlcTwoChannelPIMSVisibleBase {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  ConfigSpace (RlcTwoChannelPIMSVariableTargetEdge gamma gamma')


def rlc_twoChannelFailureVisibleBase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelPIMSVisibleBase gamma gamma' :=
  fun e => (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1


def rlc_twoChannelSuccessVisibleBase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelPIMSVisibleBase gamma gamma' :=
  fun e => eta.1 e.1

abbrev RlcTwoChannelFailureVisibleFibre {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :=
  {rho : RlcTwoChannelEdgeFailure gamma gamma' //
    rlc_twoChannelFailureVisibleBase hclosure rho = base}

abbrev RlcTwoChannelSuccessVisibleFibre {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :=
  {eta : RlcTwoChannelEdgeSuccess gamma gamma' //
    rlc_twoChannelSuccessVisibleBase eta = base}



def RlcTwoChannelPIMSPooledVisibleFibreCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  forall base : RlcTwoChannelPIMSVisibleBase gamma gamma',
    Fintype.card (RlcTwoChannelFailureVisibleFibre hclosure base) <=
      Fintype.card (RlcTwoChannelSuccessVisibleFibre base)



def RlcTwoChannelPIMSPooledVisibleCompatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  rlc_twoChannelSuccessVisibleBase eta =
    rlc_twoChannelFailureVisibleBase hclosure rho





def RlcTwoChannelPIMSPooledScoreCompatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (N : Nat) (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho eta ∧
    FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N

private noncomputable def rlc_sigmaEmbedding
    {alpha : Type*} {beta gamma : alpha -> Type*}
    (f : forall a, beta a ↪ gamma a) : (Sigma beta) ↪ Sigma gamma where
  toFun x := ⟨x.1, f x.1 x.2⟩
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hab : a = b := congrArg Sigma.fst h
    subst b
    have hout : f a x = f a y := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hxy : x = y := (f a).injective hout
    subst y
    rfl

private noncomputable def rlc_twoChannelVisibleFibreEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure)
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      RlcTwoChannelSuccessVisibleFibre base :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (hcapacity base))



noncomputable def rlc_twoChannelPooledVisibleEmbeddingOfCapacity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' :=
  (Equiv.sigmaFiberEquiv
      (rlc_twoChannelFailureVisibleBase hclosure)).symm.toEmbedding |>.trans
    (rlc_sigmaEmbedding fun base =>
      rlc_twoChannelVisibleFibreEmbedding hcapacity base) |>.trans
    (Equiv.sigmaFiberEquiv
      (rlc_twoChannelSuccessVisibleBase
        (gamma := gamma) (gamma' := gamma'))).toEmbedding

theorem rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho
      (rlc_twoChannelPooledVisibleEmbeddingOfCapacity hcapacity rho) := by
  have hbase :=
    (rlc_twoChannelVisibleFibreEmbedding hcapacity
      (rlc_twoChannelFailureVisibleBase hclosure rho)
      ⟨rho, rfl⟩).2
  simpa [RlcTwoChannelPIMSPooledVisibleCompatible,
    rlc_twoChannelPooledVisibleEmbeddingOfCapacity, rlc_sigmaEmbedding] using
      hbase



def rlc_twoChannelPooledVisibleFibreEmbeddingOfGlobal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (J : RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma')
    (hJ : forall rho,
      RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (J rho))
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      RlcTwoChannelSuccessVisibleFibre base where
  toFun rho := ⟨J rho.1, (hJ rho.1).trans rho.2⟩
  inj' := by
    intro rho sigma h
    apply Subtype.ext
    exact J.injective (congrArg Subtype.val h)



theorem
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪
          RlcTwoChannelEdgeSuccess gamma gamma',
        forall rho,
          RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (J rho) := by
  constructor
  · intro hcapacity
    exact ⟨rlc_twoChannelPooledVisibleEmbeddingOfCapacity hcapacity,
      rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible hcapacity⟩
  · rintro ⟨J, hJ⟩ base
    exact Fintype.card_le_of_embedding
      (rlc_twoChannelPooledVisibleFibreEmbeddingOfGlobal J hJ base)



theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      RlcTwoChannelEdgeCodeHall gamma gamma'
        (RlcTwoChannelPIMSPooledVisibleCompatible hclosure) := by
  rw [rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding]
  exact
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding
      hclosure


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
      gamma gamma' (RlcTwoChannelPIMSPooledVisibleCompatible hclosure)
  exact
    (rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall
      hclosure).mp hcapacity




theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma'
      (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq N
        (RlcTwoChannelPIMSPooledScoreCompatible hclosure N) hHall
  intro rho eta hcompatible
  exact hcompatible.2



theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma'
      (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual
    gamma gamma' hq (pow_nonneg (Real.sqrt_nonneg q) N) hclosure
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall
      gamma gamma' hclosure hq N hHall

end

end StatMech.Universality
