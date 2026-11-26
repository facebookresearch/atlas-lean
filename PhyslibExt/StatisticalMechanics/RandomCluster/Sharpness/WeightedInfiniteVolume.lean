/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodicRepair
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointConnectivity
public import MathlibExt.Probability.Configuration.Prokhorov

/-!
# Infinite-volume weighted phases and the common critical point

Finite and infinite-volume measures for each phase, the infinite-volume crossing probability, and
the common critical point of all phases under a positivity-transport hypothesis.

## i. Overview

`weightedPhaseFiniteMeasure` is the wired measure on the box for the couplings of phase `a`.
`weightedPhaseInfiniteVolume` is its weak limit and `weightedPhaseInfiniteTheta` the infinite-volume
percolation probability. The phases share a zero set, hence a critical point, provided positivity
transfers between phases (`WeightedPhasePositivityTransport`). This version of
`covariant_weighted_phase_common_critical` is conditional on `htransport :
CovariantWeightedPhasePositivityTransport`; `WeightedPhaseCommonCritical` proves that hypothesis and
gives the unconditional statement. The `Weighted*` files extend the OSSS sharpness argument to
random-cluster models with inhomogeneous, periodic couplings `J` on `ℤ^d`. A phase map `phase : Site
d → P` to a finite set of phases, with `PhaseCovariant J phase phaseJ`, describes how translates of
the box see the couplings. The final results are
`WeightedPhaseCommonCritical.covariant_weighted_phase_common_critical` (all phases share one
critical point) and
`WeightedThreshold.weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness` (sharp threshold),
together with subcritical exponential decay.

## ii. Key results

- `weightedPhaseInfiniteVolume_isLimit`: the infinite-volume measure is the limit of the finite
  ones.
- `covariant_weighted_phase_common_critical`: common critical point, conditional on `htransport`.

## iii. Table of contents

- A. Finite and infinite-volume measures
- B. Diagonal convergence and envelopes
- C. Positivity transport and the common critical point

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
open Set Filter Topology

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedInfiniteVolume

open StatMech.Lattice FK Percolation RevealmentConstruction
open WiredBoxDifferential
open FKSharpnessWeightedPeriodic

/-! ## A. Finite and infinite-volume measures -/

/-- The wired random-cluster probability mass function on the active edges of the box with couplings
  `J`. -/
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

/-- The wired random-cluster measure on the box of radius `n` for the couplings of phase `a`, pushed
  to configurations of `ℤ^d`. -/
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
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance⟩

/-- The infinite-volume measure of phase `a`: the weak limit of the finite wired measures. -/
noncomputable def weightedPhaseInfiniteVolume
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (CompactSpace.tendsto_subseq
    (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta)).choose

lemma weightedPhaseInfiniteVolume_isLimit
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
    (CompactSpace.tendsto_subseq
      (fun n => weightedPhaseFiniteMeasure d n
        phaseJ a hJ q beta hq hbeta)).choose_spec
  exact ⟨phi, hphi, hlim⟩

/-- The infinite-volume probability that the origin is connected to the boundary of the box of
  radius `k`. -/
noncomputable def weightedPhaseInfiniteShell
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) (k : Nat) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)

/-- The infinite-volume percolation probability of phase `a`. -/
noncomputable def weightedPhaseInfiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) : Real :=
  ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)

lemma weightedPhaseInfiniteTheta_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    0 <= weightedPhaseInfiniteTheta d phaseJ a hJ q beta hq hbeta :=
  ENNReal.toReal_nonneg

lemma weightedPhaseFiniteShell_tendsto_infinite
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

lemma weightedPhaseInfiniteShell_tendsto_theta
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

/-! ## B. Diagonal convergence and envelopes -/

lemma PhaseCovariant.phaseCoupling_translate
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

/-- The finite-volume crossing probabilities of every phase converge along the diagonal to the
  infinite-volume percolation probability. -/
def WeightedPhaseDiagonalTailConvergence
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) : Prop :=
  forall a beta (hbeta : 0 < beta) (hq : 0 < q),
    Tendsto (weightedPhaseWiredTheta d phaseJ a q beta) atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta))

lemma weightedPhaseEnvelope_tendsto_infinite_of_diagonal
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

/-! ## C. Positivity transport and the common critical point -/

/-- Positivity of `θ` transfers between phases: if one phase percolates at `β`, every phase does. -/
def WeightedPhasePositivityTransport {P : Type*}
    (thetaInf : P -> Real -> Real) : Prop :=
  forall a b beta, 0 < thetaInf a beta ↔ 0 < thetaInf b beta

/-- The infinite-volume percolation probability of each phase, as a function of `β`. -/
noncomputable def weightedPhaseThetaProfile
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (a : P) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta hq hbeta
  else 0

lemma weightedPhaseThetaProfile_nonneg
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

/-- Positivity transport for the phases of a phase-covariant coupling. -/
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

lemma phase_zeroSet_eq_of_positivityTransport
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

lemma phase_critical_eq_of_positivityTransport
    {P : Type*} (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a b : P) :
    sSup {beta | thetaInf a beta = 0} =
      sSup {beta | thetaInf b beta = 0} := by
  rw [phase_zeroSet_eq_of_positivityTransport thetaInf hnonneg htransport a b]

lemma phaseEnvelope_zeroSet_eq_phase
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

lemma phaseEnvelope_critical_eq_phase
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (htransport : WeightedPhasePositivityTransport thetaInf)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => thetaInf b beta) = 0} =
      sSup {beta | thetaInf a beta = 0} := by
  rw [phaseEnvelope_zeroSet_eq_phase thetaInf hnonneg htransport a]

lemma covariant_weighted_phase_common_critical
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
