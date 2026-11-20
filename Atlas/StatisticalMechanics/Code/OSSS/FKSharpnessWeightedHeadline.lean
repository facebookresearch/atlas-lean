/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.OSSS.FKSharpnessWeightedPhasewiseMeanField

open scoped BigOperators
open Finset Set MeasureTheory

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedHeadline

open Lattice FK IsingFK
open RevealmentConstruction
open WiredBoxDifferential
open FKSharpnessWeightedPeriodic
open FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedCoherentLimit
open FKSharpnessWeightedThreshold
open FKSharpnessWeightedPhasewiseMeanField



private theorem allClosed_not_connToBdry (d n : Nat) :
    Not (ConnToBdry (boxGraph d n) (boxBoundary d n)
      (fun _ => false) (boxOrigin d n)) := by
  rintro ⟨y, hy, hconn⟩
  have hopen : openSub (boxGraph d n) (fun _ => false) = ⊥ := by
    ext x z
    simp [openSub_adj]
  unfold FK.Connected at hconn
  rw [hopen, SimpleGraph.reachable_bot] at hconn
  subst y
  change (0 : Site d) ∈ vertexBoundary d n at hy
  exact hy.2 (by intro i; simp)




theorem weightedPhaseFiniteBoundaryMass_lt_one
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
      Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxBdryConnEvent d n) < 1 := by
  classical
  let Jbox := phaseBoxCoupling phaseJ a n
  let mu := activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
    (betaParams Jbox beta) q
  let A := liftCfg (boxActiveEdge d n) ⁻¹' boxBdryConnEvent d n
  have hmass :
      ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d n) =
        ∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega := by
    simpa [A, mu, Jbox] using
      (weightedPhaseFiniteMeasure_real_eq d n phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta (boxBdryConnEvent d n)
        (measurableSet_boxBdryConnEvent d n))
  rw [hmass]
  have hterm : forall omega,
      A.indicator (fun _ => (1 : Real)) omega * mu omega <= mu omega := by
    intro omega
    by_cases homega : omega ∈ A
    · simp [Set.indicator_of_mem homega]
    · rw [Set.indicator_of_notMem homega, zero_mul]
      exact (activeBCProb_pos (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
        (betaParams_lt_one Jbox beta) (zero_lt_one.trans_le hq) omega).le
  have hlift :
      liftCfg (boxActiveEdge d n)
          (fun _ : (boxGraph d n).edgeSet => false) =
        (fun _ : Sym2 (Site d) => false) := by
    funext e
    simp [liftCfg]
  have hclosed : (fun _ : (boxGraph d n).edgeSet => false) ∉ A := by
    rw [show (fun _ : (boxGraph d n).edgeSet => false) ∈ A ↔
        liftCfg (boxActiveEdge d n)
          (fun _ : (boxGraph d n).edgeSet => false) ∈
            boxBdryConnEvent d n by rfl, hlift]
    exact allClosed_not_connToBdry d n
  have hstrict :
      A.indicator (fun _ => (1 : Real))
          (fun _ : (boxGraph d n).edgeSet => false) *
          mu (fun _ => false) < mu (fun _ => false) := by
    rw [Set.indicator_of_notMem hclosed, zero_mul]
    exact activeBCProb_pos (boxGraph d n) (wiredBoxBoundaryGraph d n)
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one Jbox beta) (zero_lt_one.trans_le hq) _
  calc
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega) <
        ∑ omega, mu omega :=
      Finset.sum_lt_sum (fun omega _ => hterm omega)
        ⟨fun _ => false, Finset.mem_univ _, hstrict⟩
    _ = 1 := activeBCProb_sum_eq_one (boxGraph d n)
      (wiredBoxBoundaryGraph d n)
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one Jbox beta) (zero_lt_one.trans_le hq)





theorem weightedPeriodicSharpness_all_radii_of_two_le
    (d : Nat) (hd : 2 <= d)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    exists beta0 betaC kappa : Real,
      0 < betaC /\ betaC < beta0 /\ 0 < kappa /\
      (forall a : P,
        sSup (BetaCMatch.bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a)) = betaC) /\
      (forall a beta,
        betaC <= beta -> beta <= beta0 ->
        (kappa / Fintype.card P) *
            weightedPhaseSharpConstant d Jmin Jmax beta0 *
            (beta - betaC) <=
          weightedPhaseThetaProfile d phaseJ
            (hcov.phaseCoupling_pos hsurj
              (fun e => hJmin.trans_le (hJlo e))) q
            (zero_lt_one.trans_le hq) a beta) /\
      forall gamma, (hgamma : 0 < gamma) -> gamma < betaC ->
        exists c : Real, 0 < c /\ forall a : P, forall n : Nat,
          ((weightedPhaseFiniteMeasure d n phaseJ a
              (hcov.phaseCoupling_pos hsurj
                (fun e => hJmin.trans_le (hJlo e)) a)
              q gamma (zero_lt_one.trans_le hq) hgamma :
              ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <=
            Real.exp (-(c * (n : Real))) := by
  classical
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  obtain ⟨beta0, betaC, kappa, hbetaC, hcut, hkappa,
      hcritical, hmean, hdecay⟩ :=
    weightedPeriodicSharpness_of_two_le d hd J Jmin Jmax hJmin hJlo hJhi
      phase phaseJ hsurj hcov q hq
  refine ⟨beta0, betaC, kappa, hbetaC, hcut, hkappa, hcritical, ?_, ?_⟩
  · intro a beta hbeta hupper
    rcases hbeta.eq_or_lt with rfl | hbeta
    · have hnonneg := weightedPhaseThetaProfile_nonneg d phaseJ hp q
        (zero_lt_one.trans_le hq) a betaC
      simpa using hnonneg
    · exact hmean a beta hbeta hupper
  · intro gamma hgamma hgammaC
    obtain ⟨c2, hc2, hlarge⟩ := hdecay gamma hgamma hgammaC
    let u : P -> Real := fun a =>
      ((weightedPhaseFiniteMeasure d 1 phaseJ a (hp a) q gamma
          (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d 1)
    let m := Finset.univ.sup' Finset.univ_nonempty u
    have hu0 : forall a, 0 <= u a := fun _ => measureReal_nonneg
    have hum : forall a, u a <= m := fun a =>
      Finset.le_sup' u (Finset.mem_univ a)
    have hm0 : 0 <= m := by
      obtain ⟨a⟩ := (inferInstance : Nonempty P)
      exact (hu0 a).trans (hum a)
    have hm1 : m < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).2 (by
      intro a ha
      simpa [u, hp] using weightedPhaseFiniteBoundaryMass_lt_one
        d 1 phaseJ a (hp a) q gamma hq hgamma)
    let r := (m + 1) / 2
    have hr0 : 0 < r := by dsimp [r]; linarith
    have hr1 : r < 1 := by dsimp [r]; linarith
    have hmr : m <= r := by dsimp [r]; linarith
    let c1 := -Real.log r
    have hc1 : 0 < c1 := by
      dsimp [c1]
      exact neg_pos.mpr (Real.log_neg hr0 hr1)
    let c := min c1 c2
    have hc : 0 < c := lt_min hc1 hc2
    refine ⟨c, hc, ?_⟩
    intro a n
    rcases n with _ | n
    · simpa only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero] using
        (measureReal_le_one :
        ((weightedPhaseFiniteMeasure d 0 phaseJ a (hp a) q gamma
            (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) :
          Measure _).real (boxBdryConnEvent d 0) <= 1)
    rcases n with _ | n
    · have hone :
          ((weightedPhaseFiniteMeasure d 1 phaseJ a (hp a) q gamma
              (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) :
            Measure _).real (boxBdryConnEvent d 1) <=
              Real.exp (-(c * (1 : Real))) := by
        calc
          ((weightedPhaseFiniteMeasure d 1 phaseJ a (hp a) q gamma
              (zero_lt_one.trans_le hq) hgamma : ProbabilityMeasure _) :
            Measure _).real (boxBdryConnEvent d 1) = u a := rfl
          _ <= m := hum a
          _ <= r := hmr
          _ = Real.exp (-(c1 * (1 : Real))) := by
            dsimp [c1]
            rw [neg_mul, neg_neg, mul_one, Real.exp_log hr0]
          _ <= Real.exp (-(c * (1 : Real))) := by
            rw [Real.exp_le_exp]
            have hcc1 : c <= c1 := min_le_left _ _
            linarith
      simpa using hone
    · have hn : 2 <= n + 2 := by omega
      exact (hlarge a (n + 2) hn).trans (by
        rw [Real.exp_le_exp]
        have hcc2 : c <= c2 := min_le_right _ _
        have hn0 : (0 : Real) <= n + 2 := by positivity
        nlinarith)

end FKSharpnessWeightedHeadline
end OSSS
end StatMech
