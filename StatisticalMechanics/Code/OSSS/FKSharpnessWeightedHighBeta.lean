/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.OSSS.FKSharpnessWeightedThreshold
import Code.IsingFK.PcUpperAllDimensions

open scoped BigOperators
open Finset Set Filter Topology
open MeasureTheory

namespace StatMech
namespace FK



theorem edgeProductW_cross_params
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 < pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 < pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProductW G pf1 a * edgeProductW G pf2 b <=
      edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b) := by
  classical
  unfold edgeProductW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro e he
    apply mul_nonneg
    · split <;> linarith [hpf1 e, hpf1' e]
    · split <;> linarith [hpf2 e, hpf2' e]
  · intro e he
    have hinf : (a ⊓ b) e = (a e && b e) := rfl
    have hsup : (a ⊔ b) e = (a e || b e) := rfl
    rw [hinf, hsup]
    cases ha : a e <;> cases hb : b e
    all_goals simp
    all_goals nlinarith [hle e]

theorem bcWeightW_cross_params
    {V : Type*} [Fintype V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 < pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 < pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcWeightW G C pf1 q a * bcWeightW G C pf2 q b <=
      bcWeightW G C pf1 q (a ⊓ b) * bcWeightW G C pf2 q (a ⊔ b) := by
  classical
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C b <=
        q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C le_rfl a b)
  have hedge := edgeProductW_cross_params G hpf1 hpf1' hpf2 hpf2' hle a b
  have hedge0 : 0 <= edgeProductW G pf1 a * edgeProductW G pf2 b :=
    mul_nonneg (edgeProductW_pos G hpf1 hpf1' a).le
      (edgeProductW_pos G hpf2 hpf2' b).le
  have hcluster0 : 0 <=
      q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b) := by
    positivity
  unfold bcWeightW
  calc
    (edgeProductW G pf1 a * q ^ numClustersBC G C a) *
          (edgeProductW G pf2 b * q ^ numClustersBC G C b) =
        (edgeProductW G pf1 a * edgeProductW G pf2 b) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C b) := by ring
    _ <= (edgeProductW G pf1 a * edgeProductW G pf2 b) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C (a ⊔ b)) :=
      mul_le_mul_of_nonneg_left hcluster hedge0
    _ <= (edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b)) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C (a ⊔ b)) :=
      mul_le_mul_of_nonneg_right hedge hcluster0
    _ = (edgeProductW G pf1 (a ⊓ b) * q ^ numClustersBC G C (a ⊓ b)) *
          (edgeProductW G pf2 (a ⊔ b) * q ^ numClustersBC G C (a ⊔ b)) := by
      ring

theorem bcProbW_mono_params
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 < pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 < pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf1 q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf2 q omega := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ1 : 0 < bcZW G C pf1 q := bcZW_pos G C hpf1 hpf1' hq0
  have hZ2 : 0 < bcZW G C pf2 q := bcZW_pos G C hpf2 hpf2' hq0
  have hcross : forall a b,
      bcProbW G C pf1 q a * bcProbW G C pf2 q b <=
        bcProbW G C pf1 q (a ⊓ b) * bcProbW G C pf2 q (a ⊔ b) := by
    intro a b
    unfold bcProbW
    rw [div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
    exact bcWeightW_cross_params G C hpf1 hpf1' hpf2 hpf2' hle hq a b
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun omega => bcProbW_nonneg G C hpf1 hpf1' hq0 omega
  · exact fun omega => bcProbW_nonneg G C hpf2 hpf2' hq0 omega
  · rw [bcProbW_sum_eq_one G C hpf1 hpf1' hq0,
      bcProbW_sum_eq_one G C hpf2 hpf2' hq0]
  · exact hcross

theorem bcProbW_const
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    bcProbW G C (fun _ => p) q omega = bcProb G C p q omega := by
  classical
  congr 1

theorem wiredFinite_shell_le_weightedPhaseFinite
    (d k R : Nat) (hkR : k <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Lattice.Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmin : Real) (hJlo : forall e, Jmin <= phaseJ a e)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmin : p <= 1 - Real.exp (-(beta * Jmin))) :
    (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxBdryConnEvent d k) <=
      ((OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteMeasure
          d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxBdryConnEvent d k) := by
  classical
  let pf := betaParams
    (OSSS.FKSharpnessWeightedPeriodic.phaseBoxCoupling phaseJ a R) beta
  have hpf : forall e, 0 < pf e :=
    betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpf1 : forall e, pf e < 1 := betaParams_lt_one _ beta
  have hparam : forall e, p <= pf e := by
    intro e
    have hcoupling : Jmin <= phaseJ a (Sym2.map Subtype.val e) := hJlo _
    have hexp : Real.exp (-(beta * phaseJ a (Sym2.map Subtype.val e))) <=
        Real.exp (-(beta * Jmin)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact hpmin.trans (by
      unfold pf betaParams
      dsimp [OSSS.FKSharpnessWeightedPeriodic.phaseBoxCoupling,
        OSSS.FKSharpnessWeightedPeriodic.boxCoupling]
      linarith)
  have hmono := bcProbW_mono_params
    (boxGraph d R) (OSSS.WiredBoxDifferential.wiredBoxBoundaryGraph d R)
    (pf1 := fun _ => p) (pf2 := pf)
    (fun _ => hp) (fun _ => hp1) hpf hpf1 hparam hq
    (isIncreasing_connToBdryEventLE d hkR)
  calc
    (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxBdryConnEvent d k) =
        ∑ omega, (connToBdryEventLE d hkR).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (boxGraph d R) (boxBoundary d R) p q omega := by
      rw [boxBdryConnEvent_eq_boxRestrict_preimage d hkR,
        fkgq_wiredFiniteMeasure_real_boxRestrictEvent R hp hp1
          (zero_lt_one.trans_le hq) (connToBdryEventLE d hkR)
          (measurableSet_boxRestrict_connToBdryEventLE d hkR)]
    _ <= ∑ omega, (connToBdryEventLE d hkR).indicator
          (fun _ => (1 : Real)) omega * bcProbW
            (boxGraph d R) (OSSS.WiredBoxDifferential.wiredBoxBoundaryGraph d R)
              pf q omega := by
      simpa only [bcProbW_const, bcProb_clique_eq_wiredFkProb] using hmono
    _ = ((OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteMeasure
          d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxBdryConnEvent d k) := by
      symm
      exact OSSS.FKSharpnessWeightedCoherentLimit.weightedPhaseFiniteMeasure_shell_eq
        d hkR phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta

theorem fkTheta_le_weightedPhaseInfiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Lattice.Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmin : Real) (hJlo : forall e, Jmin <= phaseJ a e)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmin : p <= 1 - Real.exp (-(beta * Jmin))) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) <=
      OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteTheta
        d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta := by
  classical
  let muW := fun R =>
    ((OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteMeasure
      d R phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta :
      ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
      Measure (ConfigSpace (Sym2 (Lattice.Site d))))
  let muH := fun R =>
    ((wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
      Measure (ConfigSpace (Sym2 (Lattice.Site d))))
  have hshell : forall k,
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
          Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxBdryConnEvent d k) <=
        OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteShell
          d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta k := by
    intro k
    obtain ⟨phi, hphi, hweighted⟩ :=
      OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseFiniteShell_tendsto_infinite
        d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
    let A : Set (ConfigSpace (Sym2 (boxVerts d k))) :=
      {omega | IsingFK.ConnToBdry (boxGraph d k) (boxBoundary d k) omega
        (IsingFK.boxOrigin d k)}
    have hhomRaw := (fkgq_wired_infinite_measure k hp hp1 hq
      (S := A) (isIncreasing_connToBdryEvent k)).comp hphi.tendsto_atTop
    have hAeq : boxRestrict d k ⁻¹' A = boxBdryConnEvent d k := rfl
    rw [hAeq] at hhomRaw
    have hhom : Tendsto
        (fun n => (muH (phi n)).real (boxBdryConnEvent d k)) atTop
        (nhds (((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
          Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (boxBdryConnEvent d k))) := by
      simpa [muH, Function.comp_def] using hhomRaw
    have hweighted' : Tendsto
        (fun n => (muW (phi n)).real (boxBdryConnEvent d k)) atTop
        (nhds (OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteShell
          d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta k)) := by
      simpa [muW] using hweighted k
    apply le_of_tendsto_of_tendsto hhom hweighted'
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop k)]
      with n hkn
    exact wiredFinite_shell_le_weightedPhaseFinite
      d k (phi n) hkn phaseJ a hJ Jmin hJlo q beta p hq hbeta hp hp1 hpmin
  have hhomTheta : Tendsto
      (fun k => ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
          Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (boxBdryConnEvent d k)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
    exact boxBdryConnEvent_real_tendsto_percolation
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Lattice.Site d)))) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d))))
  have hweightedTheta :=
    OSSS.FKSharpnessWeightedInfiniteVolume.weightedPhaseInfiniteShell_tendsto_theta
      d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  exact le_of_tendsto_of_tendsto hhomTheta hweightedTheta
    (Eventually.of_forall hshell)

end FK

namespace OSSS
namespace FKSharpnessWeightedHighBeta

open Lattice FK
open FKSharpnessWeightedPeriodic
open FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedThreshold

theorem phaseCoupling_lower
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (hsurj : Function.Surjective phase)
    {Jmin : Real} (hJlo : forall e, Jmin <= J e) :
    forall a e, Jmin <= phaseJ a e := by
  intro a e
  obtain ⟨x, rfl⟩ := hsurj a
  rw [← hcov x e]
  exact hJlo _



theorem exists_weightedSelectedPhaseSum_pos_of_two_le
    (d : Nat) (hd : 2 <= d) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    exists betaStar : Real, 0 < betaStar /\
      0 < weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) betaStar := by
  classical
  let pc := fkPc d q
  let p := (pc + 1) / 2
  have hpc0 : 0 < pc := fkPc_pos_of_two_le hd hq
  have hpc1 : pc < 1 := fkPc_lt_one_of_two_le hd hq
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hpcp : pc < p := by dsimp [p]; linarith
  have htheta : 0 < fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) :=
    frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans_le hq) hpcp
  let betaStar := -Real.log (1 - p) / Jmin
  have hremain : 0 < 1 - p := sub_pos.mpr hp1
  have hremain1 : 1 - p < 1 := by linarith
  have hbetaStar : 0 < betaStar := by
    dsimp [betaStar]
    exact div_pos (neg_pos.mpr (Real.log_neg hremain hremain1)) hJmin
  have hparam : 1 - Real.exp (-(betaStar * Jmin)) = p := by
    have hmul : betaStar * Jmin = -Real.log (1 - p) := by
      dsimp [betaStar]
      field_simp
    rw [hmul, neg_neg, Real.exp_log hremain]
    ring
  let hpPhase := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hloPhase := phaseCoupling_lower hcov hsurj hJlo
  have hphase : forall a,
      0 < weightedPhaseThetaProfile d phaseJ hpPhase q
        (zero_lt_one.trans_le hq) a betaStar := by
    intro a
    unfold weightedPhaseThetaProfile
    rw [dif_pos hbetaStar]
    exact htheta.trans_le (FK.fkTheta_le_weightedPhaseInfiniteTheta
      d phaseJ a (hpPhase a) Jmin (hloPhase a)
        q betaStar p hq hbetaStar hp hp1 hparam.ge)
  refine ⟨betaStar, hbetaStar, ?_⟩
  unfold weightedSelectedPhaseSum
  exact Finset.sum_pos (fun a ha => hphase a) Finset.univ_nonempty



theorem exists_weightedSelectedPhaseHighBetaWitness_of_two_le
    (d : Nat) (hd : 2 <= d) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    exists beta0 : Real,
      weightedSelectedPhaseHighBetaWitness d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) beta0 := by
  classical
  obtain ⟨betaStar, hbetaStar, hsum⟩ :=
    exists_weightedSelectedPhaseSum_pos_of_two_le
      d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq
  refine ⟨betaStar + 1, betaStar, hbetaStar, by linarith, hsum⟩

end FKSharpnessWeightedHighBeta
end OSSS
end StatMech
