/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.OSSS.FKSharpnessWeightedHighBeta

open scoped BigOperators
open Finset Set Filter Topology MeasureTheory

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedPhasewiseMeanField

open Lattice FK Percolation
open BetaThresholdBound IntegrationSubcritical
open FKSharpnessWeightedPeriodic
open FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedThreshold
open FKSharpnessWeightedCoherentLimit
open FKSharpnessWeightedSelectedLaws
open FKSharpnessWeightedPhaseTransport
open FKSharpnessWeightedPhaseClose



def UniformPhaseDensityComparison {P : Type*}
    (theta : P -> Real -> Real) (betaC beta0 : Real) : Prop :=
  exists kappa : Real, 0 < kappa /\
    forall a b beta, betaC < beta -> beta <= beta0 ->
      kappa * theta b beta <= theta a beta






theorem weightedPhaseFinite_shell_le_wiredFinite
    (d k R : Nat) (hkR : k <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmax : Real) (hJhi : forall e, phaseJ a e <= Jmax)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) <=
      (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) := by
  classical
  let pf := betaParams (phaseBoxCoupling phaseJ a R) beta
  have hpf : forall e, 0 < pf e :=
    betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpf1 : forall e, pf e < 1 := betaParams_lt_one _ beta
  have hparam : forall e, pf e <= p := by
    intro e
    have hcoupling : phaseJ a (Sym2.map Subtype.val e) <= Jmax := hJhi _
    have hexp : Real.exp (-(beta * Jmax)) <=
        Real.exp (-(beta * phaseJ a (Sym2.map Subtype.val e))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (by
      unfold pf betaParams phaseBoxCoupling boxCoupling
      linarith : pf e <= 1 - Real.exp (-(beta * Jmax))).trans hpmax
  have hmono := FK.bcProbW_mono_params
    (boxGraph d R) (WiredBoxDifferential.wiredBoxBoundaryGraph d R)
    (pf1 := pf) (pf2 := fun _ => p)
    hpf hpf1 (fun _ => hp) (fun _ => hp1) hparam hq
    (isIncreasing_connToBdryEventLE d hkR)
  calc
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) =
        ∑ omega, (connToBdryEventLE d hkR).indicator
            (fun _ => (1 : Real)) omega *
          bcProbW (boxGraph d R)
            (WiredBoxDifferential.wiredBoxBoundaryGraph d R) pf q omega := by
      exact weightedPhaseFiniteMeasure_shell_eq
        d hkR phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
    _ <= ∑ omega, (connToBdryEventLE d hkR).indicator
          (fun _ => (1 : Real)) omega *
        bcProbW (boxGraph d R)
          (WiredBoxDifferential.wiredBoxBoundaryGraph d R)
          (fun _ => p) q omega := hmono
    _ = (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) := by
      rw [boxBdryConnEvent_eq_boxRestrict_preimage d hkR,
        fkgq_wiredFiniteMeasure_real_boxRestrictEvent R hp hp1
          (zero_lt_one.trans_le hq) (connToBdryEventLE d hkR)
          (measurableSet_boxRestrict_connToBdryEventLE d hkR)]
      apply Finset.sum_congr rfl
      intro omega homega
      rw [FK.bcProbW_const]
      change _ * bcProb (boxGraph d R)
          (boundaryCliqueGraph (boxBoundary d R)) p q omega = _
      rw [bcProb_clique_eq_wiredFkProb]



theorem weightedPhaseInfiniteTheta_le_fkTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmax : Real) (hJhi : forall e, phaseJ a e <= Jmax)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
    weightedPhaseInfiniteTheta d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta <=
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
  classical
  let muW := fun R =>
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let muH := fun R =>
    ((wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d))))
  have hshell : forall k,
      weightedPhaseInfiniteShell d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta k <=
        ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k) := by
    intro k
    obtain ⟨phi, hphi, hweighted⟩ :=
      weightedPhaseFiniteShell_tendsto_infinite
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
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k))) := by
      simpa [muH, Function.comp_def] using hhomRaw
    have hweighted' : Tendsto
        (fun n => (muW (phi n)).real (boxBdryConnEvent d k)) atTop
        (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta k)) := by
      simpa [muW] using hweighted k
    apply le_of_tendsto_of_tendsto hweighted' hhom
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop k)]
      with n hkn
    exact weightedPhaseFinite_shell_le_wiredFinite
      d k (phi n) hkn phaseJ a hJ Jmax hJhi q beta p hq hbeta
        hp hp1 hpmax
  have hweightedTheta := weightedPhaseInfiniteShell_tendsto_theta
    d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  have hhomTheta : Tendsto
      (fun k => ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
    exact boxBdryConnEvent_real_tendsto_percolation
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d))))
  exact le_of_tendsto_of_tendsto hweightedTheta hhomTheta
    (Eventually.of_forall hshell)



theorem phaseCoupling_upper
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (hsurj : Function.Surjective phase)
    {Jmax : Real} (hJhi : forall e, J e <= Jmax) :
    forall a e, phaseJ a e <= Jmax := by
  intro a e
  obtain ⟨x, rfl⟩ := hsurj a
  rw [← hcov x e]
  exact hJhi _



theorem weightedThreshold_pos_of_highBetaWitness
    (d : Nat) (hd : 2 <= d)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta0) :
    0 < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  classical
  let hpPhase := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  obtain ⟨betaStar, hbetaStar, hstar0, hstar⟩ := hhigh
  have hbeta0 : 0 < beta0 := hbetaStar.trans hstar0
  have hJmax : 0 < Jmax := by
    let e : Sym2 (Site d) := s((0 : Site d), (0 : Site d))
    exact hJmin.trans_le (hJlo e) |>.trans_le (hJhi e)
  let p : Real := 1 / (4 * d)
  have hdpos : (0 : Real) < d := by exact_mod_cast (by omega : 0 < d)
  have hdTwo : (2 : Real) <= d := by exact_mod_cast hd
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p < 1 := by
    dsimp [p]
    rw [div_lt_one (by positivity)]
    nlinarith [hdTwo]
  have hsmall : (2 * d : Real) * p < 1 := by
    dsimp [p]
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith [hdTwo]
  let betaSmall := -Real.log (1 - p) / Jmax
  have hremain : 0 < 1 - p := sub_pos.mpr hp1
  have hremain1 : 1 - p < 1 := by linarith
  have hbetaSmall : 0 < betaSmall := by
    dsimp [betaSmall]
    exact div_pos (neg_pos.mpr (Real.log_neg hremain hremain1)) hJmax
  let betaLow := min betaSmall (beta0 / 2)
  have hbetaLow : 0 < betaLow := by
    dsimp [betaLow]
    exact lt_min hbetaSmall (half_pos hbeta0)
  have hlow0 : betaLow <= beta0 := by
    have hle : betaLow <= beta0 / 2 := min_le_right _ _
    linarith
  have hpmax : 1 - Real.exp (-(betaLow * Jmax)) <= p := by
    have hmul : betaSmall * Jmax = -Real.log (1 - p) := by
      dsimp [betaSmall]
      field_simp
    have hparamSmall : 1 - Real.exp (-(betaSmall * Jmax)) = p := by
      rw [hmul, neg_neg, Real.exp_log hremain]
      ring
    have hprod : betaLow * Jmax <= betaSmall * Jmax :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hJmax.le
    have hexp : Real.exp (-(betaSmall * Jmax)) <=
        Real.exp (-(betaLow * Jmax)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hprod)
    linarith
  have hphaseHi : forall a e, phaseJ a e <= Jmax :=
    phaseCoupling_upper hcov hsurj hJhi
  have hthetaHom : fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 :=
    FK.fkTheta_eq_zero_of_lt (by omega) hp hp1 hq hsmall
  have hphaseZero : forall a,
      weightedPhaseThetaProfile d phaseJ hpPhase q
        (zero_lt_one.trans_le hq) a betaLow = 0 := by
    intro a
    unfold weightedPhaseThetaProfile
    rw [dif_pos hbetaLow]
    apply le_antisymm
    · exact (weightedPhaseInfiniteTheta_le_fkTheta
        d phaseJ a (hpPhase a) Jmax (hphaseHi a)
          q betaLow p hq hbetaLow hp hp1 hpmax).trans_eq hthetaHom
    · exact weightedPhaseInfiniteTheta_nonneg
        d phaseJ a (hpPhase a) q betaLow
          (zero_lt_one.trans_le hq) hbetaLow
  have hsumZero : weightedSelectedPhaseSum d phaseJ hpPhase q
      (zero_lt_one.trans_le hq) betaLow = 0 := by
    unfold weightedSelectedPhaseSum
    exact Finset.sum_eq_zero fun a ha => hphaseZero a
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hpPhase Jmin Jmax q beta0 hJmin hq
      (by simpa [hpPhase] using
        (⟨betaStar, hbetaStar, hstar0, hstar⟩ :
          weightedSelectedPhaseHighBetaWitness d phaseJ hpPhase q
            (zero_lt_one.trans_le hq) beta0))
  by_contra hnot
  have hbetaOneLow : betaOne < betaLow :=
    lt_of_le_of_lt (not_lt.mp hnot) hbetaLow
  have hmf := weightedSelectedPhaseSum_meanField_lower
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 betaLow hq hne hbetaOneLow hlow0
  have hfactor : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
      (betaLow - betaOne) :=
    mul_pos (weightedPhaseSharpConstant_pos d hJmin)
      (sub_pos.mpr hbetaOneLow)
  have hsumPos : 0 < weightedSelectedPhaseSum d phaseJ hpPhase q
      (zero_lt_one.trans_le hq) betaLow := hfactor.trans_le (by
        simpa [hpPhase, betaOne] using hmf)
  rw [hsumZero] at hsumPos
  exact lt_irrefl 0 hsumPos






theorem weightedPhaseInfinite_singleOpen_measurable_bound
    (d N : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (eN : (boxGraph d N).edgeSet)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    weightedOpenTolerance
        (betaParams (phaseJ a) beta (WiredBoxDifferential.boxActiveEdge d N eN)) q *
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
        (setOpen (WiredBoxDifferential.boxActiveEdge d N eN) ⁻¹' A) <=
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
          Measure (ConfigSpace (Sym2 (Site d)))).real A := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  let p := betaParams (phaseJ a) beta
    (WiredBoxDifferential.boxActiveEdge d N eN)
  have hp : 0 < p := by
    dsimp [p, betaParams]
    have hprod := mul_pos hbeta
      (hJ (WiredBoxDifferential.boxActiveEdge d N eN))
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hprod)
    linarith
  have hp1 : p < 1 := by
    dsimp [p, betaParams]
    linarith [Real.exp_pos
      (-(beta * phaseJ a (WiredBoxDifferential.boxActiveEdge d N eN)))]
  exact pattern_bound_of_cylinders mu
    (setOpen (WiredBoxDifferential.boxActiveEdge d N eN))
    (measurable_setOpen _) (weightedOpenTolerance p q)
    (weightedOpenTolerance_pos hp hp1 hq).le
    (weightedPhaseInfinite_singleOpen_fullCylinder_bound
      d N phaseJ a hJ q beta hq hbeta eN) A hA


theorem div_q_le_weightedOpenTolerance
    {p0 p q : Real} (hp0p : p0 <= p)
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    p0 / q <= weightedOpenTolerance p q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hdenpos : 0 < p + q * (1 - p) :=
    add_pos hp (mul_pos hqpos (sub_pos.mpr hp1))
  have hdenle : p + q * (1 - p) <= q := by
    have hmul : 0 <= p * (q - 1) :=
      mul_nonneg hp.le (sub_nonneg.mpr hq)
    nlinarith
  unfold weightedOpenTolerance
  apply (div_le_div_iff₀ hqpos hdenpos).2
  calc
    p0 * (p + q * (1 - p)) <= p * (p + q * (1 - p)) :=
      mul_le_mul_of_nonneg_right hp0p hdenpos.le
    _ <= p * q := mul_le_mul_of_nonneg_left hdenle hp.le



noncomputable def weightedUniformOpenConstant
    (betaOne Jmin q : Real) : Real :=
  (1 - Real.exp (-(betaOne * Jmin))) / q

theorem weightedUniformOpenConstant_pos
    {betaOne Jmin q : Real}
    (hbetaOne : 0 < betaOne) (hJmin : 0 < Jmin) (hq : 1 <= q) :
    0 < weightedUniformOpenConstant betaOne Jmin q := by
  unfold weightedUniformOpenConstant
  have hprod : 0 < betaOne * Jmin := mul_pos hbetaOne hJmin
  have hnum : 0 < 1 - Real.exp (-(betaOne * Jmin)) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hprod)
    linarith
  exact div_pos hnum (zero_lt_one.trans_le hq)

theorem weightedUniformOpenConstant_le
    {betaOne beta Jmin Jedge q : Real}
    (hbetaOne : 0 < betaOne) (hbeta : betaOne < beta)
    (hJmin : 0 < Jmin) (hJedge : Jmin <= Jedge)
    (hq : 1 <= q) :
    weightedUniformOpenConstant betaOne Jmin q <=
      weightedOpenTolerance (1 - Real.exp (-(beta * Jedge))) q := by
  let p0 := 1 - Real.exp (-(betaOne * Jmin))
  let p := 1 - Real.exp (-(beta * Jedge))
  have hJedgePos : 0 < Jedge := hJmin.trans_le hJedge
  have hp0 : 0 < p0 := by
    dsimp [p0]
    have := Real.exp_lt_one_iff.mpr
      (neg_neg_of_pos (mul_pos hbetaOne hJmin))
    linarith
  have hp : 0 < p := by
    dsimp [p]
    have := Real.exp_lt_one_iff.mpr
      (neg_neg_of_pos (mul_pos (hbetaOne.trans hbeta) hJedgePos))
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * Jedge))]
  have hprod : betaOne * Jmin <= beta * Jedge := by
    calc
      betaOne * Jmin <= beta * Jmin :=
        mul_le_mul_of_nonneg_right hbeta.le hJmin.le
      _ <= beta * Jedge :=
        mul_le_mul_of_nonneg_left hJedge (hbetaOne.trans hbeta).le
  have hp0p : p0 <= p := by
    dsimp [p0, p]
    have hexp : Real.exp (-(beta * Jedge)) <=
        Real.exp (-(betaOne * Jmin)) :=
      Real.exp_le_exp.mpr (neg_le_neg hprod)
    linarith
  change p0 / q <= weightedOpenTolerance p q
  exact div_q_le_weightedOpenTolerance hp0p hp hp1 hq


theorem forceOpenFinset_real_bound_of_single
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure mu]
    (F : Finset (Sym2 (Site d))) (c : Real) (hc : 0 <= c)
    (hone : forall e, e ∈ F -> forall A,
      MeasurableSet A -> c * mu.real (setOpen e ⁻¹' A) <= mu.real A)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    c ^ F.card * mu.real (forceOpenFinset F ⁻¹' A) <= mu.real A := by
  revert hone A
  induction F using Finset.induction with
  | empty =>
      intro hone A hA
      have hempty : forceOpenFinset (∅ : Finset (Sym2 (Site d))) = id := by
        funext omega e
        simp [forceOpenFinset]
      simp [hempty]
  | @insert e F he ih =>
      intro hone A hA
      have honeF : forall f, f ∈ F -> forall B,
          MeasurableSet B -> c * mu.real (setOpen f ⁻¹' B) <= mu.real B := by
        intro f hf
        exact hone f (Finset.mem_insert_of_mem hf)
      have hinner := ih honeF (setOpen e ⁻¹' A)
        (hA.preimage (measurable_setOpen e))
      have hedge := hone e (Finset.mem_insert_self e F) A hA
      have hpre : forceOpenFinset (insert e F) ⁻¹' A =
          forceOpenFinset F ⁻¹' (setOpen e ⁻¹' A) := by
        rw [forceOpenFinset_insert]
        rfl
      rw [Finset.card_insert_of_notMem he, hpre, pow_succ]
      calc
        c ^ F.card * c * mu.real
              (forceOpenFinset F ⁻¹' (setOpen e ⁻¹' A)) =
            c * (c ^ F.card * mu.real
              (forceOpenFinset F ⁻¹' (setOpen e ⁻¹' A))) := by ring
        _ <= c * mu.real (setOpen e ⁻¹' A) :=
          mul_le_mul_of_nonneg_left hinner hc
        _ <= mu.real A := hedge

private theorem phasewise_boxEdge_has_active_rep
    (d n : Nat) (e : Sym2 (Site d)) (he : e ∈ boxEdges d n) :
    exists eN : (boxGraph d n).edgeSet,
      WiredBoxDifferential.boxActiveEdge d n eN = e := by
  induction e with
  | h x y =>
      obtain ⟨hx, hy, hxy⟩ := mem_boxEdges_iff.mp he
      let xb : boxVerts d n := ⟨x, hx⟩
      let yb : boxVerts d n := ⟨y, hy⟩
      have hb : (boxGraph d n).Adj xb yb := hxy
      let eN : (boxGraph d n).edgeSet := ⟨s(xb, yb), by
        rw [SimpleGraph.mem_edgeSet]
        exact hb⟩
      refine ⟨eN, ?_⟩
      change edgeIncl d n s(xb, yb) = s(x, y)
      simp [edgeIncl, xb, yb]


theorem weightedPhaseInfinite_forceOpen_box_bound
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmin : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= phaseJ a e)
    (q betaOne beta : Real) (hq : 1 <= q)
    (hbetaOne : 0 < betaOne) (hbeta : betaOne < beta)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    weightedUniformOpenConstant betaOne Jmin q ^ (boxEdges d n).card *
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) (hbetaOne.trans hbeta) :
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (forceOpenFinset (boxEdges d n) ⁻¹' A) <=
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) (hbetaOne.trans hbeta) :
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real A := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) (hbetaOne.trans hbeta)
  apply forceOpenFinset_real_bound_of_single mu (boxEdges d n)
    (weightedUniformOpenConstant betaOne Jmin q)
    (weightedUniformOpenConstant_pos hbetaOne hJmin hq).le
  · intro e he B hB
    obtain ⟨eN, rfl⟩ := phasewise_boxEdge_has_active_rep d n e he
    have hconstant := weightedUniformOpenConstant_le
      hbetaOne hbeta hJmin
        (hJlo (WiredBoxDifferential.boxActiveEdge d n eN)) hq
    have hmass : 0 <= mu.real
        (setOpen (WiredBoxDifferential.boxActiveEdge d n eN) ⁻¹' B) :=
      ENNReal.toReal_nonneg
    have hlower : weightedUniformOpenConstant betaOne Jmin q *
          mu.real (setOpen (WiredBoxDifferential.boxActiveEdge d n eN) ⁻¹' B) <=
        weightedOpenTolerance
            (betaParams (phaseJ a) beta
              (WiredBoxDifferential.boxActiveEdge d n eN)) q *
          mu.real (setOpen (WiredBoxDifferential.boxActiveEdge d n eN) ⁻¹' B) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [betaParams] using hconstant) hmass
    exact hlower.trans (by
      simpa only [mu] using
        (weightedPhaseInfinite_singleOpen_measurable_bound
          d n phaseJ a hJ q beta hq (hbetaOne.trans hbeta) eN B hB))
  · exact hA




theorem uniformPhaseDensityComparison_of_threshold_pos
    (d : Nat) {P : Type*} [Finite P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q betaOne beta0 : Real) (hq : 1 <= q)
    (hbetaOne : 0 < betaOne) :
    UniformPhaseDensityComparison
      (weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq)) betaOne beta0 := by
  classical
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let rep : P -> Site d := fun a => Classical.choose (hsurj a)
  have hrep : forall a, phase (rep a) = a :=
    fun a => Classical.choose_spec (hsurj a)
  let displacement : P × P -> Site d :=
    fun ab => rep ab.2 - rep ab.1
  obtain ⟨n, hn⟩ := Lattice.finite_subset_box (Set.range displacement)
    (Set.finite_range displacement)
  let c := weightedUniformOpenConstant betaOne Jmin q
  let kappa := c ^ (boxEdges d n).card
  have hc : 0 < c := weightedUniformOpenConstant_pos hbetaOne hJmin hq
  have hkappa : 0 < kappa := pow_pos hc _
  refine ⟨kappa, hkappa, ?_⟩
  intro a b beta hbeta hupper
  have hbetaPos : 0 < beta := hbetaOne.trans hbeta
  simp only [weightedPhaseThetaProfile, dif_pos hbetaPos]
  let x := rep a
  let y := rep b
  let z := y - x
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (x - y)
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a (hp a) q beta
      (zero_lt_one.trans_le hq) hbetaPos
  have hmeasure :
      (weightedPhaseInfiniteVolume d phaseJ b (hp b) q beta
          (zero_lt_one.trans_le hq) hbetaPos :
          Measure (ConfigSpace (Sym2 (Site d)))) =
        mu.map (ConfigSpace.shift g) := by
    have ht := covariantWeightedSelectedPhaseTranslation
      J phase phaseJ (fun e => hJmin.trans_le (hJlo e))
        hsurj hcov q hq beta hbetaPos x y
    simpa [x, y, g, mu, hrep a, hrep b, hp] using ht
  have hgz : g • z = origin d := by
    change (x - y) + (y - x) = origin d
    rw [show (origin d) = 0 by rfl]
    abel
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
        ConfigSpace (Sym2 (Site d))) ⁻¹' percolationEvent d =
      clusterInfiniteEvent d z := by
    have hs := shift_preimage_clusterInfiniteEvent (d := d) g z
    rw [hgz] at hs
    simpa [percolationEvent] using hs
  have hmapreal :
      (mu.map (ConfigSpace.shift g)).real (percolationEvent d) =
        mu.real (clusterInfiniteEvent d z) := by
    have hperco : MeasurableSet (percolationEvent d) := by
      simpa [percolationEvent, clusterInfiniteEvent] using
        (measurableSet_clusterInfiniteEvent (d := d) (origin d))
    rw [Measure.real, Measure.real,
      Measure.map_apply (ConfigSpace.measurable_shift g) hperco, hpre]
  have hthetaB :
      weightedPhaseInfiniteTheta d phaseJ b (hp b) q beta
          (zero_lt_one.trans_le hq) hbetaPos =
        mu.real (clusterInfiniteEvent d z) := by
    unfold weightedPhaseInfiniteTheta
    rw [hmeasure, hmapreal]
  have hzbox : z ∈ box d n := by
    apply hn
    refine ⟨(a, b), ?_⟩
    rfl
  have h0box : origin d ∈ box d n := by
    intro i
    simp [origin]
  have hconn : forall omega,
      Connected d (forceOpenFinset (boxEdges d n) omega) z (origin d) :=
    fun omega => box_allOpen_connected omega hzbox h0box
  have hsubset : clusterInfiniteEvent d z ⊆
      forceOpenFinset (boxEdges d n) ⁻¹'
        clusterInfiniteEvent d (origin d) :=
    clusterInfiniteEvent_subset_forceOpen_preimage
      (boxEdges d n) z (origin d) hconn
  have hmono : mu.real (clusterInfiniteEvent d z) <=
      mu.real (forceOpenFinset (boxEdges d n) ⁻¹'
        clusterInfiniteEvent d (origin d)) :=
    measureReal_mono hsubset
  have hforce := weightedPhaseInfinite_forceOpen_box_bound
    d n phaseJ a (hp a) Jmin hJmin
      (FKSharpnessWeightedHighBeta.phaseCoupling_lower
        hcov hsurj hJlo a)
      q betaOne beta hq hbetaOne hbeta
      (clusterInfiniteEvent d (origin d))
      (measurableSet_clusterInfiniteEvent (d := d) (origin d))
  calc
    kappa * weightedPhaseInfiniteTheta d phaseJ b (hp b) q beta
        (zero_lt_one.trans_le hq) hbetaPos =
      kappa * mu.real (clusterInfiniteEvent d z) := by rw [hthetaB]
    _ <= kappa * mu.real
        (forceOpenFinset (boxEdges d n) ⁻¹'
          clusterInfiniteEvent d (origin d)) :=
      mul_le_mul_of_nonneg_left hmono hkappa.le
    _ <= weightedPhaseInfiniteTheta d phaseJ a (hp a) q beta
        (zero_lt_one.trans_le hq) hbetaPos := by
      simpa [kappa, c, mu, weightedPhaseInfiniteTheta,
        percolationEvent] using hforce



theorem individual_ge_uniform_mul_sum_div_card
    {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Real -> Real) (betaC beta0 : Real)
    (hcomparison : UniformPhaseDensityComparison theta betaC beta0) :
    exists kappa : Real, 0 < kappa /\
      forall a beta, betaC < beta -> beta <= beta0 ->
        (kappa / Fintype.card P) * (∑ b : P, theta b beta) <=
          theta a beta := by
  obtain ⟨kappa, hkappa, hcompare⟩ := hcomparison
  refine ⟨kappa, hkappa, ?_⟩
  intro a beta hbeta hupper
  have hsum : (∑ b : P, kappa * theta b beta) <=
      ∑ _b : P, theta a beta := by
    exact Finset.sum_le_sum fun b _ => hcompare a b beta hbeta hupper
  have hcard : 0 < (Fintype.card P : Real) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, nsmul_eq_mul, <- Finset.mul_sum] at hsum
  calc
    (kappa / Fintype.card P) * (∑ b : P, theta b beta) =
        (kappa * (∑ b : P, theta b beta)) /
          (Fintype.card P : Real) := by ring
    _ <= ((Fintype.card P : Real) * theta a beta) /
          (Fintype.card P : Real) :=
      (div_le_div_iff_of_pos_right hcard).2 hsum
    _ = theta a beta := by field_simp




theorem weightedIndividualPhase_meanField_lower_of_uniformComparison
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcomparison : UniformPhaseDensityComparison
      (weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq))
      (beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) beta0) :
    exists kappa : Real, 0 < kappa /\ forall a beta,
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta ->
      beta <= beta0 ->
      (kappa / Fintype.card P) *
          weightedPhaseSharpConstant d Jmin Jmax beta0 *
          (beta - beta1 (fun b n => Sig
            (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <=
        weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a beta := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  obtain ⟨kappa, hkappa, hphase⟩ :=
    individual_ge_uniform_mul_sum_div_card
      (weightedPhaseThetaProfile d phaseJ hp q
        (zero_lt_one.trans_le hq)) betaOne beta0 hcomparison
  refine ⟨kappa, hkappa, ?_⟩
  intro a beta hbeta hupper
  have hsum := weightedSelectedPhaseSum_meanField_lower
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 beta hq hne hbeta hupper
  have hfactor : 0 <= kappa / (Fintype.card P : Real) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hfactor
  have htransport := hphase a beta hbeta hupper
  calc
    _ <= (kappa / Fintype.card P) *
        weightedSelectedPhaseSum d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) beta := by
      simpa only [mul_assoc] using hscaled
    _ <= _ := by simpa [weightedSelectedPhaseSum] using htransport




theorem weightedUniformPhaseDensityComparison_of_two_le
    (d : Nat) (hd : 2 <= d)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    exists beta0 : Real,
      UniformPhaseDensityComparison
        (weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq))
        (beta1 (fun b n => Sig
          (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) beta0 := by
  obtain ⟨beta0, hhigh⟩ :=
    FKSharpnessWeightedHighBeta.exists_weightedSelectedPhaseHighBetaWitness_of_two_le
      d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  have hbetaOne : 0 < betaOne := by
    dsimp [betaOne]
    exact weightedThreshold_pos_of_highBetaWitness
      d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hhigh
  refine ⟨beta0, ?_⟩
  exact uniformPhaseDensityComparison_of_threshold_pos
    d J Jmin hJmin hJlo phase phaseJ hsurj hcov
      q betaOne beta0 hq hbetaOne



theorem weightedIndividualPhase_meanField_lower_of_two_le
    (d : Nat) (hd : 2 <= d)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    exists beta0 : Real,
      exists kappa : Real, 0 < kappa /\ forall a beta,
        beta1 (fun b n => Sig
          (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta ->
        beta <= beta0 ->
        (kappa / Fintype.card P) *
            weightedPhaseSharpConstant d Jmin Jmax beta0 *
            (beta - beta1 (fun b n => Sig
              (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <=
          weightedPhaseThetaProfile d phaseJ
            (hcov.phaseCoupling_pos hsurj
              (fun e => hJmin.trans_le (hJlo e))) q
            (zero_lt_one.trans_le hq) a beta := by
  obtain ⟨beta0, hhigh⟩ :=
    FKSharpnessWeightedHighBeta.exists_weightedSelectedPhaseHighBetaWitness_of_two_le
      d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq
  refine ⟨beta0, ?_⟩
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e)))
      Jmin Jmax q beta0 hJmin hq hhigh
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  have hbetaOne : 0 < betaOne := by
    dsimp [betaOne]
    exact weightedThreshold_pos_of_highBetaWitness
      d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hhigh
  have hcomparison : UniformPhaseDensityComparison
      (weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq)) betaOne beta0 :=
    uniformPhaseDensityComparison_of_threshold_pos
      d J Jmin hJmin hJlo phase phaseJ hsurj hcov
        q betaOne beta0 hq hbetaOne
  exact weightedIndividualPhase_meanField_lower_of_uniformComparison
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 hq hne (by simpa [betaOne] using hcomparison)




theorem weightedPhasePhysical_one_sub_lower
    (d n : Nat) (hn : 2 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) (hbeta0 : beta <= beta0) (a : P) :
    Real.exp (-(beta0 * Jmax)) ^ (2 * d) <=
      1 - ((weightedPhaseFiniteMeasure d n phaseJ a
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e)) a)
        q beta (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d n) := by
  let k := n / 2
  have hk : 1 <= k := by
    dsimp [k]
    omega
  have hlo := FKSharpnessWeightedHighBeta.phaseCoupling_lower
    hcov hsurj hJlo
  have hhi := phaseCoupling_upper hcov hsurj hJhi
  have hphysical :=
    FKSharpnessWeightedIntegration.weightedPhasePhysical_le_localized_half
    d n hn phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e)))
      a q beta hq hbeta
  have hgap :=
    FKSharpnessWeightedIntegration.weightedLocalizedTheta_one_sub_lower
    d k (phaseJ a) Jmin Jmax q beta beta0 hJmin (hlo a) (hhi a)
      hq hbeta hbeta0
  have hprofile :
      FKSharpnessWeightedLocalized.weightedLocalizedTheta
          d k (phaseJ a) q beta =
        FKSharpnessWeightedStrict.weightedPhaseProfile
          d phaseJ a q beta k := by
    rw [FKSharpnessWeightedStrict.weightedPhaseProfile,
      if_neg (Nat.ne_of_gt hk)]
    rfl
  rw [hprofile] at hgap
  exact hgap.trans (sub_le_sub_left hphysical 1)



theorem prefactor_exp_decay_of_one_sub_lower
    {I : Type*} (u : I -> Nat -> Real) (C epsilon rate : Real)
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon <= 1)
    (hrate : 0 < rate)
    (hu0 : forall i n, 2 <= n -> 0 <= u i n)
    (hgap : forall i n, 2 <= n -> epsilon <= 1 - u i n)
    (hdecay : forall i n, 2 <= n ->
      u i n <= C * Real.exp (-(rate * (n : Real)))) :
    exists c : Real, 0 < c /\ forall i n, 2 <= n ->
      u i n <= Real.exp (-(c * (n : Real))) := by
  let A := 1 - epsilon
  have hA0 : 0 <= A := by
    dsimp [A]
    linarith
  have hA1 : A < 1 := by
    dsimp [A]
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos one_pos hC) hA1
  have hmC : C * A ^ m <= 1 := by
    have := (lt_div_iff₀ hC).mp hm
    nlinarith
  let c := rate / (m + 1 : Nat)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro i n hn
  have hu := hu0 i n hn
  have huA : u i n <= A := by
    have := hgap i n hn
    dsimp [A]
    linarith
  have hpow : u i n ^ (m + 1) <=
      Real.exp (-(rate * (n : Real))) := by
    calc
      u i n ^ (m + 1) = u i n ^ m * u i n := by rw [pow_succ]
      _ <= A ^ m * u i n := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hu huA m) hu
      _ <= A ^ m * (C * Real.exp (-(rate * (n : Real)))) := by
        exact mul_le_mul_of_nonneg_left (hdecay i n hn) (pow_nonneg hA0 m)
      _ = (C * A ^ m) * Real.exp (-(rate * (n : Real))) := by ring
      _ <= Real.exp (-(rate * (n : Real))) := by
        exact (mul_le_of_le_one_left (Real.exp_pos _).le hmC)
  have hexpPow :
      Real.exp (-(c * (n : Real))) ^ (m + 1) =
        Real.exp (-(rate * (n : Real))) := by
    rw [<- Real.exp_nat_mul]
    congr 1
    dsimp [c]
    field_simp
  apply (pow_le_pow_iff_left₀ (n := m + 1)
    hu (Real.exp_pos _).le (by omega)).mp
  rwa [hexpPow]






theorem weightedPeriodicSharpness_of_two_le
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
        betaC < beta -> beta <= beta0 ->
        (kappa / Fintype.card P) *
            weightedPhaseSharpConstant d Jmin Jmax beta0 *
            (beta - betaC) <=
          weightedPhaseThetaProfile d phaseJ
            (hcov.phaseCoupling_pos hsurj
              (fun e => hJmin.trans_le (hJlo e))) q
            (zero_lt_one.trans_le hq) a beta) /\
      forall gamma, (hgamma : 0 < gamma) -> gamma < betaC ->
        exists c : Real, 0 < c /\ forall a : P, forall n : Nat, 2 <= n ->
          ((weightedPhaseFiniteMeasure d n phaseJ a
              (hcov.phaseCoupling_pos hsurj
                (fun e => hJmin.trans_le (hJlo e)) a)
              q gamma (zero_lt_one.trans_le hq) hgamma :
              ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <=
            Real.exp (-(c * (n : Real))) := by
  obtain ⟨beta0, hhigh⟩ :=
    FKSharpnessWeightedHighBeta.exists_weightedSelectedPhaseHighBetaWitness_of_two_le
      d hd J Jmin hJmin hJlo phase phaseJ hsurj hcov q hq
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaC := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    exact weightedThreshold_pos_of_highBetaWitness
      d hd J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hhigh
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcut : betaC < beta0 := by
    dsimp [betaC]
    exact weightedHighBetaWitness_strict_cutoff
      d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcomparison : UniformPhaseDensityComparison
      (weightedPhaseThetaProfile d phaseJ hp q
        (zero_lt_one.trans_le hq)) betaC beta0 :=
    uniformPhaseDensityComparison_of_threshold_pos
      d J Jmin hJmin hJlo phase phaseJ hsurj hcov
        q betaC beta0 hq hbetaC
  obtain ⟨kappa, hkappa, hmean⟩ :=
    weightedIndividualPhase_meanField_lower_of_uniformComparison
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hne (by simpa [hp, betaC] using hcomparison)
  refine ⟨beta0, betaC, kappa, hbetaC, hcut, hkappa, ?_, ?_, ?_⟩
  · intro a
    simpa [betaC, hp] using
      (weightedThreshold_eq_selectedPhaseCritical
        d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 hq hne (by simpa [betaC] using hcut) a)
  · intro a beta hbeta hupper
    simpa [betaC] using hmean a beta (by simpa [betaC] using hbeta) hupper
  · intro gamma hgamma hgammaC
    let beta := (gamma + betaC) / 2
    let delta := (betaC - gamma) / 4
    have hdelta : 0 < delta := by
      dsimp [delta]
      linarith
    have hbetaC' : beta < betaC := by
      dsimp [beta]
      linarith
    have hbeta0 : beta <= beta0 := (hbetaC'.trans hcut).le
    have hleft : 0 < beta - 2 * delta := by
      dsimp [beta, delta]
      linarith
    have htemp : beta - 2 * delta = gamma := by
      dsimp [beta, delta]
      ring
    have hlt : beta < beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
      simpa [betaC] using hbetaC'
    obtain ⟨Q, hQ, hdecay⟩ :=
      weightedPhasePhysical_subcritical_decay_of_threshold
        d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q delta beta beta0 hq hbeta0 hdelta hleft hlt
    simp only [htemp] at hdecay
    let epsilon := Real.exp (-(beta0 * Jmax)) ^ (2 * d)
    let rate := delta / (3 * Q)
    have hbeta0pos : 0 < beta0 := hbetaC.trans hcut
    have hJmax : 0 < Jmax := by
      let e : Sym2 (Site d) := s((0 : Site d), (0 : Site d))
      exact hJmin.trans_le (hJlo e) |>.trans_le (hJhi e)
    have hexp0 : 0 < Real.exp (-(beta0 * Jmax)) := Real.exp_pos _
    have hexp1 : Real.exp (-(beta0 * Jmax)) <= 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact pow_pos hexp0 _
    have hepsilon1 : epsilon <= 1 := by
      dsimp [epsilon]
      exact pow_le_one₀ hexp0.le hexp1
    have hrate : 0 < rate := by
      dsimp [rate]
      exact div_pos hdelta (mul_pos (by norm_num) hQ)
    have hcard : 0 < (Fintype.card P : Real) := by
      exact_mod_cast Fintype.card_pos
    let u := fun a n =>
      ((weightedPhaseFiniteMeasure d n phaseJ a
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e)) a)
          q gamma (zero_lt_one.trans_le hq) hgamma :
          ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n)
    have hu0 : forall a n, 2 <= n -> 0 <= u a n := by
      intro a n hn
      exact measureReal_nonneg
    have hgap : forall a n, 2 <= n -> epsilon <= 1 - u a n := by
      intro a n hn
      simpa [epsilon, u, hp] using
        (weightedPhasePhysical_one_sub_lower d n hn J Jmin Jmax hJmin
          hJlo hJhi phase phaseJ hsurj hcov q gamma beta0 hq hgamma
          (hgammaC.trans hcut).le a)
    have hdecay' : forall a n, 2 <= n ->
        u a n <= (Fintype.card P : Real) *
          Real.exp (-(rate * (n : Real))) := by
      intro a n hn
      have ha := hdecay a n hn
      have hexponent :
          -(((n : Real) / (3 * Q)) * delta) =
            -(rate * (n : Real)) := by
        dsimp [rate]
        ring
      rw [hexponent] at ha
      simpa [u, hp] using ha
    obtain ⟨c, hc, hpure⟩ := prefactor_exp_decay_of_one_sub_lower
      u (Fintype.card P : Real) epsilon rate hcard hepsilon hepsilon1
        hrate hu0 hgap hdecay'
    exact ⟨c, hc, by
      intro a n hn
      simpa [u] using hpure a n hn⟩

end FKSharpnessWeightedPhasewiseMeanField
end OSSS
end StatMech
