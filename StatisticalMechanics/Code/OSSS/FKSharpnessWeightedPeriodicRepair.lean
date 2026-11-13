/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.OSSS.FKSharpnessWeightedPeriodic
import Code.OSSS.FKSharpnessWeightedDomain

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedPeriodicRepair

open Lattice FK RevealmentConstruction RevealmentTranslation
open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open FKSharpnessWeightedPeriodic FKSharpnessWeightedDomain

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V]
variable [Fintype W] [DecidableEq W]



theorem edgeProductW_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (omega : ConfigSpace (Sym2 W)) :
    edgeProductW G pfV (reCfgIso sigma omega) = edgeProductW H pfW omega := by
  unfold edgeProductW reCfgIso
  symm
  apply Finset.prod_bij'
      (i := fun e _ => Sym2.map sigma.symm e)
      (j := fun e _ => Sym2.map sigma e)
  · intro e he
    exact fvs_mem_edgeFinset_map_symm G H sigma hsigma he
  · intro e he
    exact fvs_mem_edgeFinset_map G H sigma hsigma he
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [Sym2.map_map]
    have hmap : Sym2.map (sigma ∘ sigma.symm) e = e := by
      rw [show (sigma ∘ sigma.symm : W -> W) = id by
        funext w
        exact sigma.apply_symm_apply w]
      exact congrFun Sym2.map_id e
    rw [hmap]
    have hpfe := hpf (Sym2.map sigma.symm e)
    rw [Sym2.map_map, hmap] at hpfe
    rw [hpfe]



theorem bcWeightW_boundaryClique_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (q : Real) (omega : ConfigSpace (Sym2 W)) :
    bcWeightW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) =
      bcWeightW H (boundaryCliqueGraph bdryW) pfW q omega := by
  unfold bcWeightW
  rw [edgeProductW_reCfgIso G H sigma hsigma pfV pfW hpf omega,
    numClustersBC_boundaryClique, numClustersBC_boundaryClique,
    fvs_numClustersWired_reCfgIso G H bdryV bdryW sigma hsigma hbdry omega]


theorem bcProbW_boundaryClique_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (q : Real) (omega : ConfigSpace (Sym2 W)) :
    bcProbW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) =
      bcProbW H (boundaryCliqueGraph bdryW) pfW q omega := by
  have hZ : bcZW G (boundaryCliqueGraph bdryV) pfV q =
      bcZW H (boundaryCliqueGraph bdryW) pfW q := by
    unfold bcZW
    rw [← Equiv.sum_comp (reCfgIsoEquiv sigma)
      (fun eta => bcWeightW G (boundaryCliqueGraph bdryV) pfV q eta)]
    apply Finset.sum_congr rfl
    intro eta heta
    exact bcWeightW_boundaryClique_reCfgIso G H bdryV bdryW sigma
      hsigma hbdry pfV pfW hpf q eta
  unfold bcProbW
  rw [bcWeightW_boundaryClique_reCfgIso G H bdryV bdryW sigma
    hsigma hbdry pfV pfW hpf q omega, hZ]

end Relabel



noncomputable def weightedOuterInnerConn
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real)
    (x : Site d) (k : Nat) : Real :=
  Lindeberg.mean
    (activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (betaParams (boxCoupling J (2 * n)) beta) q)
    (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n)
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
      x (centeredBoundary x k) then (1 : Real) else 0)




def WeightedPhaseOffCentreStrict (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (theta : P -> Nat -> Real) (q beta : Real) : Prop :=
  forall x, x ∈ osssBoxFinset d n -> forall k, 1 <= k -> 2 * k < n ->
    weightedOuterInnerConn d n J q beta x k <= theta (phase x) k



def PeriodicWeightedNestedDominationStrict
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Prop :=
  PhaseCovariant J phase phaseJ ∧
    WeightedPhaseOffCentreStrict d n J phase
      (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta



theorem weighted_transShellEvent_mass_eq_phase
    (d k : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (x : Site d) (q beta : Real) :
    (∑ eta,
      (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta *
        bcProbW (fvs_transBoxGraph d (2 * k) x)
          (boundaryCliqueGraph (fvs_transBoxBoundary d (2 * k) x))
          (betaParams (transBoxCoupling J (2 * k) x) beta) q eta) =
      ∑ rho,
        (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho *
          bcProbW (boxGraph d (2 * k))
            (boundaryCliqueGraph (boxBoundary d (2 * k)))
            (betaParams (phaseBoxCoupling phaseJ (phase x) (2 * k)) beta)
            q rho := by
  let sigma := fvs_transEquiv d (2 * k) x
  have hmass := cdc_eventMassProb_reCfgIso_inv sigma
    (bcProbW (boxGraph d (2 * k))
      (boundaryCliqueGraph (boxBoundary d (2 * k)))
      (betaParams (phaseBoxCoupling phaseJ (phase x) (2 * k)) beta) q)
    (bcProbW (fvs_transBoxGraph d (2 * k) x)
      (boundaryCliqueGraph (fvs_transBoxBoundary d (2 * k) x))
      (betaParams (transBoxCoupling J (2 * k) x) beta) q)
    (fun eta => bcProbW_boundaryClique_reCfgIso
      (boxGraph d (2 * k)) (fvs_transBoxGraph d (2 * k) x)
      (boxBoundary d (2 * k)) (fvs_transBoxBoundary d (2 * k) x)
      sigma (fvs_transEquiv_adj d (2 * k) x)
      (fvs_transEquiv_boundary d (2 * k) x)
      (betaParams (phaseBoxCoupling phaseJ (phase x) (2 * k)) beta)
      (betaParams (transBoxCoupling J (2 * k) x) beta)
      (fun e => betaParams_transBox_map_eq_phaseBox
        J phase phaseJ hcov (2 * k) x beta e)
      q eta)
    (centeredShellEvent d k)
  rwa [reCfgIso_preimage_centeredShellEvent] at hmass


theorem weightedPhaseWiredTheta_eq_centeredShellMass
    (d k : Nat) (hk : 1 <= k) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseWiredTheta d phaseJ a q beta k =
      ∑ rho,
        (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho *
          bcProbW (boxGraph d (2 * k))
            (boundaryCliqueGraph (boxBoundary d (2 * k)))
            (betaParams (phaseBoxCoupling phaseJ a (2 * k)) beta) q rho := by
  unfold weightedPhaseWiredTheta
  change activeBCMean (boxGraph d (2 * k))
      (boundaryCliqueGraph (boxBoundary d (2 * k)))
      (betaParams (phaseBoxCoupling phaseJ a (2 * k)) beta) q
      (innerCrossInd d k) = _
  rw [activeBCMean_eq_bcProbW_lift]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rw [innerCrossInd_restrictActive_eq_centeredShell_indicator d k hk rho]
  · exact betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  · exact betaParams_lt_one _ beta
  · exact zero_lt_one.trans_le hq



theorem weightedOuterInnerConn_le_transShellMass
    (d n k : Nat) (x : Site d)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n)) :
    weightedOuterInnerConn d n J q beta x k <=
      ∑ rho,
        (ocd_innerRestrict (flc_incl hsub) ⁻¹'
          transShellEvent d k x).indicator (fun _ => (1 : Real)) rho *
        bcProbW (boxGraph d (2 * n))
          (boundaryCliqueGraph (boxBoundary d (2 * n)))
          (betaParams (boxCoupling J (2 * n)) beta) q rho := by
  let obs : ConfigSpace (boxGraph d (2 * n)).edgeSet -> Real := fun eta =>
    if ConnectedToSet d
      (liftCfg (boxActiveEdge d n)
        (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) eta))
      x (centeredBoundary x k) then 1 else 0
  unfold weightedOuterInnerConn
  change activeBCMean (boxGraph d (2 * n))
      (boundaryCliqueGraph (boxBoundary d (2 * n)))
      (betaParams (boxCoupling J (2 * n)) beta) q obs <= _
  rw [activeBCMean_eq_bcProbW_lift]
  · apply Finset.sum_le_sum
    intro rho hrho
    apply mul_le_mul_of_nonneg_right
    · unfold obs
      by_cases hc : ConnectedToSet d
          (liftCfg (boxActiveEdge d n)
            (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n))
              (restrictActive (boxGraph d (2 * n)) rho)))
          x (centeredBoundary x k)
      · rw [if_pos hc, Set.indicator_of_mem]
        exact outerInnerConn_subset_transShell d n k x hsub rho hc
      · rw [if_neg hc]
        exact Set.indicator_nonneg (fun _ => by norm_num) _
    · exact bcProbW_nonneg _ _
        (betaParams_pos
          (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
        (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) rho
  · exact betaParams_pos
      (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  · exact betaParams_lt_one _ beta
  · exact zero_lt_one.trans_le hq



theorem weightedOuterInnerConn_le_phase_strict
    (d n k : Nat) (x : Site d) (hx : x ∈ box d n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedOuterInnerConn d n J q beta x k <=
      weightedPhaseWiredTheta d phaseJ (phase x) q beta k := by
  let hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n) := by
    intro y hy i
    have hyi : ((y - x) i).natAbs <= 2 * k := hy i
    have hxi : (x i).natAbs <= n := hx i
    have hEq : y i = (y i - x i) + x i := by ring
    calc
      (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← hEq]
      _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n := by omega
  have hxdeep : x ∈ box d (2 * n - 2 * k - 1) := by
    apply box_mono d (show n <= 2 * n - 2 * k - 1 by omega)
    exact hx
  have hmargin : forall y : fvs_transBoxVerts d (2 * k) x,
      ¬ boxBoundary d (2 * n) (flc_incl hsub y) :=
    ocs_wired_margin d (2 * k) (2 * n) x hxdeep
      (show 2 * k + 1 <= 2 * n by omega) hsub
  have hlocal := weightedOuterInnerConn_le_transShellMass
    d n k x J hJ q beta hq hbeta hsub
  have hdomain := weighted_transShellEvent_domain_dominated
    d (2 * n) k x J hJ hsub hmargin hk beta q hbeta hq
  have htransport := weighted_transShellEvent_mass_eq_phase
    d k J phase phaseJ hcov x q beta
  have hphasePos : forall e, 0 < phaseJ (phase x) e := by
    intro e
    rw [← hcov x e]
    exact hJ _
  have hprofile := weightedPhaseWiredTheta_eq_centeredShellMass
    d k hk phaseJ (phase x) hphasePos q beta hq hbeta
  calc
    weightedOuterInnerConn d n J q beta x k <=
        ∑ rho,
          (ocd_innerRestrict (flc_incl hsub) ⁻¹'
            transShellEvent d k x).indicator (fun _ => (1 : Real)) rho *
          bcProbW (boxGraph d (2 * n))
            (boundaryCliqueGraph (boxBoundary d (2 * n)))
            (betaParams (boxCoupling J (2 * n)) beta) q rho := hlocal
    _ <= ∑ eta,
          (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta *
          bcProbW (fvs_transBoxGraph d (2 * k) x)
            (boundaryCliqueGraph (fvs_transBoxBoundary d (2 * k) x))
            (betaParams (transBoxCoupling J (2 * k) x) beta) q eta := hdomain
    _ = ∑ rho,
          (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho *
          bcProbW (boxGraph d (2 * k))
            (boundaryCliqueGraph (boxBoundary d (2 * k)))
            (betaParams (phaseBoxCoupling phaseJ (phase x) (2 * k)) beta)
            q rho := htransport
    _ = weightedPhaseWiredTheta d phaseJ (phase x) q beta k := hprofile.symm



theorem weightedPhaseOffCentreStrict_of_covariant
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    WeightedPhaseOffCentreStrict d n J phase
      (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta := by
  intro x hx k hk hkn
  apply weightedOuterInnerConn_le_phase_strict
    d n k x _ hk hkn J hJ phase phaseJ hcov q beta hq hbeta
  simpa [mem_osssBoxFinset] using hx



theorem periodicWeightedNestedDominationStrict_of_covariant
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    PeriodicWeightedNestedDominationStrict
      d n J phase phaseJ q beta := by
  exact ⟨hcov, weightedPhaseOffCentreStrict_of_covariant
    d n J hJ phase phaseJ hcov q beta hq hbeta⟩

end FKSharpnessWeightedPeriodicRepair
end OSSS
end StatMech
