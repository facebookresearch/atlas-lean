/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.OSSS.FKSharpnessWeightedPhaseClose

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedStrict

open Lattice FK RevealmentConstruction RevealmentTranslation
open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open AdaptiveCovLowerGeom
open FKSharpnessWeighted FKSharpnessWeightedPeriodic
open FKSharpnessWeightedPeriodicRepair
open FKSharpnessWeightedInfiniteVolume FKSharpnessWeightedCoherentLimit


noncomputable def weightedStrictDenom
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      weightedOuterInnerConn d n J q beta x j) / (n : Real)





noncomputable def weightedPhaseProfile
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (q beta : Real) (k : Nat) : Real :=
  if k = 0 then 1 else weightedPhaseWiredTheta d phaseJ a q beta k


noncomputable def weightedPhaseEnvelopeSig
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n,
    phaseEnvelope (fun a => weightedPhaseProfile d phaseJ a q beta) k

theorem weightedOuterInnerConn_nonneg
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) (j : Nat) :
    0 <= weightedOuterInnerConn d n J q beta x j := by
  apply mean_indicator_nonneg
  intro omega
  exact (activeBCProb_pos _ _
    (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) omega).le

theorem weightedOuterInnerConn_le_one
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) (j : Nat) :
    weightedOuterInnerConn d n J q beta x j <= 1 := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (betaParams (boxCoupling J (2 * n)) beta) q
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) omega).le
  have hsum : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq)
  calc
    weightedOuterInnerConn d n J q beta x j <=
        Lindeberg.mean mu (fun _ => (1 : Real)) := by
      unfold weightedOuterInnerConn Lindeberg.mean
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
      change (if ConnectedToSet d
        (liftCfg (boxActiveEdge d n)
          (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
        x (centeredBoundary x j) then (1 : Real) else 0) <= 1
      split <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hsum 1

theorem weightedOuterInnerConn_antitone
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) : Antitone (weightedOuterInnerConn d n J q beta x) := by
  intro j k hjk
  apply ReachBoxCrossing.mean_indicator_mono
  · intro omega
    exact (activeBCProb_pos _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) omega).le
  · intro omega hconn
    obtain ⟨y, hy, hxy⟩ := hconn
    rcases hxy with ⟨w⟩
    change centeredRadius x y = k at hy
    obtain ⟨z, hz, hxz⟩ :=
      openWalk_hits_centeredBoundary w (hjk.trans_eq hy.symm)
    exact ⟨z, hz, hxz⟩

theorem weightedOuterInnerConn_zero
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (x : Site d) : weightedOuterInnerConn d n J q beta x 0 = 1 := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (betaParams (boxCoupling J (2 * n)) beta) q
  have hsum : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq)
  have hall : (fun omega : ConfigSpace (boxGraph d (2 * n)).edgeSet =>
      if ConnectedToSet d
        (liftCfg (boxActiveEdge d n)
          (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega))
        x (centeredBoundary x 0) then (1 : Real) else 0) = fun _ => 1 := by
    funext omega
    rw [if_pos]
    exact ⟨x, centeredRadius_self x, connected_refl _ _⟩
  unfold weightedOuterInnerConn
  rw [hall]
  exact Lindeberg.mean_const mu hsum 1

theorem weightedPhaseProfile_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) (k : Nat) :
    0 <= weightedPhaseProfile d phaseJ a q beta k := by
  by_cases hk : k = 0
  · simp [weightedPhaseProfile, hk]
  · simp only [weightedPhaseProfile, if_neg hk]
    exact weightedPhaseWiredTheta_nonneg d phaseJ hJ a q beta
      (zero_lt_one.trans_le hq) hbeta k

@[simp] theorem weightedPhaseProfile_zero
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P) (q beta : Real) :
    weightedPhaseProfile d phaseJ a q beta 0 = 1 := by
  simp [weightedPhaseProfile]


theorem weightedPhaseProfile_tendsto_infiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Filter.Tendsto (weightedPhaseProfile d phaseJ a q beta) Filter.atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta)) := by
  have hraw := weightedPhaseWiredTheta_tendsto_infiniteTheta
    d phaseJ a hJ q beta hq hbeta
  apply hraw.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  simp [weightedPhaseProfile, Nat.ne_of_gt hk]



theorem weightedPhaseProfileEnvelope_tendsto
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Filter.Tendsto
      (phaseEnvelope (fun a => weightedPhaseProfile d phaseJ a q beta))
      Filter.atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseInfiniteTheta d phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta))) := by
  exact phaseEnvelope_tendsto _ _ fun a =>
    weightedPhaseProfile_tendsto_infiniteTheta
      d phaseJ a (hJ a) q beta hq hbeta

theorem weightedStrictDenom_pos
    (d n : Nat) (hn : 1 <= n)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < weightedStrictDenom d n J q beta := by
  let M := (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n,
      weightedOuterInnerConn d n J q beta x j)
  have hsum : 1 <= ∑ j ∈ Finset.range n,
      weightedOuterInnerConn d n J q beta 0 j := by
    rw [← weightedOuterInnerConn_zero d n J hJ q beta hq hbeta 0]
    apply Finset.single_le_sum
      (fun j _ => weightedOuterInnerConn_nonneg d n J hJ q beta hq hbeta 0 j)
    simpa using hn
  have hsup := Finset.le_sup'
    (fun x => ∑ j ∈ Finset.range n,
      weightedOuterInnerConn d n J q beta x j)
    (origin_mem_osssBoxFinset d n)
  change _ <= M at hsup
  have hM : 0 < M := lt_of_lt_of_le (zero_lt_one.trans_le hsum) hsup
  unfold weightedStrictDenom
  positivity




theorem weightedStrictDenom_le_phaseEnvelopeSig
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedStrictDenom d n J q beta <=
      8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real) := by
  let theta := fun k =>
    phaseEnvelope (fun a => weightedPhaseProfile d phaseJ a q beta) k
  let hp : forall a e, 0 < phaseJ a e :=
    hcov.phaseCoupling_pos hsurj hJ
  have htheta0 : forall k, 0 <= theta k := fun k =>
    phaseEnvelope_nonneg _
      (fun a j => weightedPhaseProfile_nonneg d phaseJ hp a q beta
        hq hbeta j) k
  have hthetaZero : theta 0 = 1 := by
    apply le_antisymm
    · apply Finset.sup'_le Finset.univ_nonempty
      intro a ha
      simp
    · obtain ⟨a⟩ := (inferInstance : Nonempty P)
      calc
        1 = weightedPhaseProfile d phaseJ a q beta 0 := by simp
        _ <= theta 0 := le_phaseEnvelope
          (fun b j => weightedPhaseProfile d phaseJ b q beta j) a 0
  have hoff := weightedPhaseOffCentreStrict_of_covariant
    d n J hJ phase phaseJ hcov q beta hq hbeta
  have hsup :
      (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
          (fun x => ∑ j ∈ Finset.range n,
            weightedOuterInnerConn d n J q beta x j) <=
        2 * weightedPhaseEnvelopeSig d n phaseJ q beta := by
    apply Finset.sup'_le
    intro x hx
    exact antitone_sum_range_le_two_profile_strict
      (weightedOuterInnerConn d n J q beta x) theta
      (weightedOuterInnerConn_nonneg d n J hJ q beta hq hbeta x)
      (weightedOuterInnerConn_antitone d n J hJ q beta hq hbeta x)
      htheta0 n
      (by rw [weightedOuterInnerConn_zero d n J hJ q beta hq hbeta x,
        hthetaZero])
      (fun k hk hstrict => by
        calc
          weightedOuterInnerConn d n J q beta x k <=
              weightedPhaseWiredTheta d phaseJ (phase x) q beta k :=
            hoff x hx k (Finset.mem_Icc.mp hk).1 hstrict
          _ = weightedPhaseProfile d phaseJ (phase x) q beta k := by
            symm
            simp [weightedPhaseProfile,
              Nat.ne_of_gt (Finset.mem_Icc.mp hk).1]
          _ <= theta k := le_phaseEnvelope
            (fun a j => weightedPhaseProfile d phaseJ a q beta j)
            (phase x) k)
      (fun k hk => by
        rw [hthetaZero]
        exact weightedOuterInnerConn_le_one d n J hJ q beta hq hbeta x k)
  unfold weightedStrictDenom weightedPhaseEnvelopeSig
  calc
    4 * (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩
          (fun x => ∑ j ∈ Finset.range n,
            weightedOuterInnerConn d n J q beta x j) / (n : Real)
        <= 4 * (2 * ∑ k ∈ Finset.range n,
          phaseEnvelope
            (fun a => weightedPhaseProfile d phaseJ a q beta) k) /
            (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsup (by norm_num)) (Nat.cast_nonneg n)
    _ = 8 * (∑ k ∈ Finset.range n,
          phaseEnvelope
            (fun a => weightedPhaseProfile d phaseJ a q beta) k) /
            (n : Real) := by ring

end FKSharpnessWeightedStrict
end OSSS
end StatMech

