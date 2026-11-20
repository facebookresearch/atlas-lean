/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.OSSS.FKSharpnessWeightedPeriodicRepair
import Code.FK.TwoPointPositiveFull
import Code.Foundations.Prokhorov

open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedInfiniteVolume

open Lattice FK Percolation RevealmentConstruction
open WiredBoxDifferential
open FKSharpnessWeightedPeriodic




noncomputable def weightedWiredActivePMF
    (d n : Nat) (J : Sym2 (boxVerts d n) -> Real)
    (hJ : forall e, 0 < J e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    PMF (ConfigSpace (boxGraph d n).edgeSet) :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal
      (activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (betaParams J beta) q omega)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [activeBCProb_sum_eq_one (boxGraph d n)
          (wiredBoxBoundaryGraph d n) (betaParams_pos hJ hbeta)
          (betaParams_lt_one J beta) hq]
      simp
    · intro omega homega
      exact (activeBCProb_pos (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (betaParams_pos hJ hbeta) (betaParams_lt_one J beta) hq omega).le


noncomputable def weightedPhaseFiniteMeasure
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  let J := phaseBoxCoupling phaseJ a n
  let hJbox : forall e, 0 < J e :=
    fun e => hJ (Sym2.map Subtype.val e)
  let mu := weightedWiredActivePMF d n J hJbox q beta hq hbeta
  ⟨mu.toMeasure.map (liftCfg (boxActiveEdge d n)),
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable⟩


noncomputable def weightedPhaseInfiniteVolume
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (prokhorov_seq_compact
    (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta)).choose



theorem weightedPhaseInfiniteVolume_isLimit
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    exists phi : Nat -> Nat, StrictMono phi ∧
      WeakConvergesTo
        (fun n => weightedPhaseFiniteMeasure d (phi n)
          phaseJ a hJ q beta hq hbeta)
        (weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta) := by
  obtain ⟨phi, hphi, hlim⟩ :=
    (prokhorov_seq_compact
      (fun n => weightedPhaseFiniteMeasure d n
        phaseJ a hJ q beta hq hbeta)).choose_spec
  exact ⟨phi, hphi, hlim⟩




noncomputable def weightedPhaseInfiniteShell
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) (k : Nat) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)


noncomputable def weightedPhaseInfiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)

theorem weightedPhaseInfiniteTheta_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    0 <= weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta :=
  ENNReal.toReal_nonneg


theorem weightedPhaseFiniteShell_tendsto_infinite
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    exists phi : Nat -> Nat, StrictMono phi ∧ forall k,
      Tendsto
        (fun n => ((weightedPhaseFiniteMeasure d (phi n)
          phaseJ a hJ q beta hq hbeta :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
            Measure (ConfigSpace (Sym2 (Site d)))).real
              (boxBdryConnEvent d k)) atTop
        (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta k)) := by
  obtain ⟨phi, hphi, hlim⟩ := weightedPhaseInfiniteVolume_isLimit
    d phaseJ a hJ q beta hq hbeta
  refine ⟨phi, hphi, fun k => ?_⟩
  exact hlim.tendsto_real_of_isClopen (isClopen_boxBdryConnEvent d k)



theorem weightedPhaseInfiniteShell_tendsto_theta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    Tendsto
      (weightedPhaseInfiniteShell d phaseJ a hJ q beta hq hbeta)
      atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta)) := by
  exact boxBdryConnEvent_real_tendsto_percolation
    ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d))))




theorem PhaseCovariant.phaseCoupling_translate
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (x y : Site d) (e : Sym2 (Site d)) :
    phaseJ (phase y) e =
      phaseJ (phase x) (translateAmbientEdge (y - x) e) := by
  rw [← hcov y e, ← hcov x (translateAmbientEdge (y - x) e)]
  unfold translateAmbientEdge
  rw [Sym2.map_map]
  apply congrArg J
  apply congrArg (fun f => Sym2.map f e)
  funext z
  simp [Function.comp_apply, add_assoc]




def WeightedPhaseDiagonalTailConvergence
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) : Prop :=
  forall a beta (hbeta : 0 < beta) (hq : 0 < q),
    Tendsto (weightedPhaseWiredTheta d phaseJ a q beta) atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta))



theorem weightedPhaseEnvelope_tendsto_infinite_of_diagonal
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (hdiag : WeightedPhaseDiagonalTailConvergence d phaseJ hJ q) :
    Tendsto
      (phaseEnvelope (fun a => weightedPhaseWiredTheta d phaseJ a q beta))
      atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseInfiniteTheta d phaseJ a (hJ a)
          q beta hq hbeta))) := by
  exact phaseEnvelope_tendsto _ _ (fun a => hdiag a beta hbeta hq)






def WeightedPhasePositivityTransport {P : Type*}
    (thetaInf : P -> Real -> Real) : Prop :=
  forall a b beta, 0 < thetaInf a beta ↔ 0 < thetaInf b beta



noncomputable def weightedPhaseThetaProfile
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (a : P) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta
  else 0

theorem weightedPhaseThetaProfile_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (a : P) (beta : Real) :
    0 <= weightedPhaseThetaProfile d phaseJ hJ q hq a beta := by
  unfold weightedPhaseThetaProfile
  split_ifs with hbeta
  · exact weightedPhaseInfiniteTheta_nonneg d phaseJ a (hJ a)
      q beta hq hbeta
  · exact le_rfl




def CovariantWeightedPhasePositivityTransport
    (d : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q) : Prop :=
  WeightedPhasePositivityTransport
    (weightedPhaseThetaProfile d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) q hq)





theorem phase_zeroSet_eq_of_positivityTransport
    {P : Type*} (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a b : P) :
    {beta | thetaInf a beta = 0} = {beta | thetaInf b beta = 0} := by
  ext beta
  constructor
  · intro ha
    change thetaInf a beta = 0 at ha
    apply le_antisymm
    · apply le_of_not_gt
      intro hbpos
      have hapos := (htransport b a beta).mp hbpos
      linarith
    · exact hnonneg b beta
  · intro hb
    change thetaInf b beta = 0 at hb
    apply le_antisymm
    · apply le_of_not_gt
      intro hapos
      have hbpos := (htransport a b beta).mp hapos
      linarith
    · exact hnonneg a beta



theorem phase_critical_eq_of_positivityTransport
    {P : Type*} (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a b : P) :
    sSup {beta | thetaInf a beta = 0} =
      sSup {beta | thetaInf b beta = 0} := by
  rw [phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport a b]



theorem phaseEnvelope_zeroSet_eq_phase
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a : P) :
    {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => thetaInf b beta) = 0} =
      {beta | thetaInf a beta = 0} := by
  ext beta
  constructor
  · intro hsup
    apply le_antisymm
    · exact (Finset.le_sup' (fun b => thetaInf b beta)
        (Finset.mem_univ a)).trans_eq hsup
    · exact hnonneg a beta
  · intro ha
    apply le_antisymm
    · apply Finset.sup'_le Finset.univ_nonempty
      intro b hb
      have hz := Set.ext_iff.mp
        (phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport b a) beta
      exact le_of_eq (hz.mpr ha)
    · exact (hnonneg a beta).trans
        (Finset.le_sup' (fun b => thetaInf b beta) (Finset.mem_univ a))



theorem phaseEnvelope_critical_eq_phase
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => thetaInf b beta) = 0} =
      sSup {beta | thetaInf a beta = 0} := by
  rw [phaseEnvelope_zeroSet_eq_phase thetaInf hnonneg htransport a]





theorem covariant_weighted_phase_common_critical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (htransport : CovariantWeightedPhasePositivityTransport
      d J phase phaseJ hJ hsurj hcov q hq)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
  apply phaseEnvelope_critical_eq_phase
  · exact weightedPhaseThetaProfile_nonneg d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) q hq
  · exact htransport

end FKSharpnessWeightedInfiniteVolume
end OSSS
end StatMech
