/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.WiredBoxSharpness
import Code.OSSS.BetaCMatch
import Code.FK.FreePercolationFull
import Code.IsingFK.PcUpperAllDimensions

open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace WiredBoxCritical

open Filter
open WiredBoxSharpness
open Lattice FK
open WiredBoxLocalized WiredBoxOffCentre
open MeasureTheory



theorem wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
    (d n : Nat) (hn : 1 <= n) (q beta : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) :
    wiredOuterInnerTheta d q beta n =
      (FK.wiredFiniteMeasure d (2 * n)
          (by
            have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
            linarith : 0 < 1 - Real.exp (-beta))
          (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (FK.boxBdryConnEvent d n) := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hevent : boxRestrict d (2 * n) ⁻¹' centeredShellEvent d n =
      FK.boxBdryConnEvent d n := by
    rw [centeredShellEvent_eq_connToBdryEventLE d n hn,
      ← FK.boxBdryConnEvent_eq_boxRestrict_preimage d (n_le_two_mul n)]
  have hmeas : MeasurableSet
      (boxRestrict d (2 * n) ⁻¹' centeredShellEvent d n) := by
    rw [hevent]
    exact FK.measurableSet_boxBdryConnEvent d n
  have hmass := FK.fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) (2 * n) hp hp1 (zero_lt_one.trans_le hq)
    (centeredShellEvent d n) hmeas
  have htheta := wiredOuterInnerTheta_eq_centeredShellMass
    d n hn q beta hq hbeta
  rw [hevent] at hmass
  change wiredOuterInnerTheta d q beta n =
    (FK.wiredFiniteMeasure d (2 * n) hp hp1
      (zero_lt_one.trans_le hq) : Measure _).real
        (FK.boxBdryConnEvent d n)
  rw [htheta]
  exact hmass.symm



theorem wiredOuterInnerTheta_tendsto_fkTheta
    (d : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredOuterInnerTheta d q beta n) atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) (q := q))) := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let a : Nat → Real := fun n =>
    (FK.wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (FK.boxBdryConnEvent d n)
  let b : Nat → Real := fun n => wiredOuterInnerTheta d q beta n
  let thetaInf := FK.fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q)
  have ha : Tendsto a atTop (nhds thetaInf) := by
    simpa [a, thetaInf] using
      FK.fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp hp1 hq
  have htwo : Tendsto (fun n : Nat => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have ha2 : Tendsto (fun n => a (2 * n)) atTop (nhds thetaInf) := ha.comp htwo
  have hlower : ∀ᶠ n in atTop, a (2 * n) <= b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (2 * n) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d n hn q beta hq hbeta]
    exact measureReal_mono
      (FK.boxBdryConnEvent_subset_le n (2 * n) hn (n_le_two_mul n))
      (measure_ne_top _ _)
  have hupper : ∀ᶠ n in atTop, b n <= a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (n + n) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p, two_mul] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d n hn q beta hq hbeta]
    let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
      {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
        (IsingFK.boxOrigin d n)}
    have hanti : Antitone (fun k =>
        (FK.wiredFiniteMeasure d (n + k) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n)) := by
      apply antitone_nat_of_succ_le
      intro k
      simpa [A, Nat.add_assoc] using
        (FK.fkgq_wired_succ (d := d) n (n + k) (Nat.le_add_right n k)
          hp hp1 hq (S := A) (isIncreasing_connToBdryEvent n))
    have h := hanti (Nat.zero_le n)
    simpa [a, Nat.add_zero, two_mul] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ha2 ha hlower hupper


theorem wiredThresholdTheta_tendsto_fkTheta_div
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredThresholdTheta d q beta0 n beta) atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) (q := q) / wiredSharpConstant d beta0)) := by
  have hraw := wiredOuterInnerTheta_tendsto_fkTheta d q beta hq hbeta
  have hdiv := hraw.div_const (wiredSharpConstant d beta0)
  simpa [wiredThresholdTheta, not_le.mpr hbeta, wiredNormalizedTheta] using hdiv



theorem wiredThresholdSet_mem_of_fkTheta_pos
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q)) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b) := by
  let L := FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) / wiredSharpConstant d beta0
  have hL : 0 < L := div_pos hTheta (wiredSharpConstant_pos d beta0)
  have hconv : Tendsto (fun n => wiredThresholdTheta d q beta0 n beta)
      atTop (nhds L) := by
    simpa [L] using
      wiredThresholdTheta_tendsto_fkTheta_div d q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 <= limsup (BetaThresholdBound.logRatio (fun n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]



theorem wiredThresholdSet_nonempty (d : Nat) (q beta0 : Real)
    (hd : 2 <= d) (hq : 1 <= q) :
    (BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n b)).Nonempty := by
  let pc := FK.fkPc d q
  let p := (pc + 1) / 2
  let beta := -Real.log (1 - p)
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd hq
  have hpc1 : pc < 1 := FK.fkPc_lt_one_of_two_le hd hq
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hpcp : pc < p := by dsimp [p]; linarith
  have hremain : 0 < 1 - p := by linarith
  have hremain1 : 1 - p < 1 := by linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    rw [neg_neg, Real.exp_log hremain]
    ring
  have hthetaP : 0 < FK.fkTheta d hp hp1
      (zero_lt_one.trans_le hq) (q := q) :=
    FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1
      (zero_lt_one.trans_le hq) hpcp
  have hthetaBeta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
    simpa only [hparam] using hthetaP
  exact ⟨beta, wiredThresholdSet_mem_of_fkTheta_pos
    d q beta0 beta hq hbeta hthetaBeta⟩


noncomputable def wiredBeta1 (d : Nat) (beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b)



noncomputable def betaFKTheta (d : Nat) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2)
  else 0

theorem betaFKTheta_eq (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    betaFKTheta d beta = FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
  simp only [betaFKTheta, dif_pos hbeta]

theorem betaFKTheta_nonneg (d : Nat) (beta : Real) :
    0 <= betaFKTheta d beta := by
  by_cases hbeta : 0 < beta
  · rw [betaFKTheta_eq d beta hbeta]
    exact FK.fkTheta_nonneg d _ _ (by norm_num) (q := 2)
  · simp [betaFKTheta, hbeta]


theorem betaFKTheta_mono (d : Nat) : Monotone (betaFKTheta d) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · rw [betaFKTheta_eq d a ha, betaFKTheta_eq d b hb]
      have hpa0 : 0 < 1 - Real.exp (-a) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -a < 0)
        linarith
      have hpa1 : 1 - Real.exp (-a) < 1 := by
        linarith [Real.exp_pos (-a)]
      have hpb0 : 0 < 1 - Real.exp (-b) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -b < 0)
        linarith
      have hpb1 : 1 - Real.exp (-b) < 1 := by
        linarith [Real.exp_pos (-b)]
      have hexp : Real.exp (-b) <= Real.exp (-a) :=
        Real.exp_le_exp.mpr (by linarith)
      have hpab : 1 - Real.exp (-a) <= 1 - Real.exp (-b) := by
        simpa only [sub_eq_add_neg, add_comm] using
          add_le_add_left (neg_le_neg hexp) 1
      exact FK.fkgq_fkTheta_monotone_in_p hpa0 hpa1 hpb0 hpb1 hpab
        (by norm_num)
    · rw [show betaFKTheta d a = 0 by simp [betaFKTheta, ha]]
      exact betaFKTheta_nonneg d b
  · have ha : ¬ 0 < a := fun h => hb (h.trans_le hab)
    simp [betaFKTheta, ha, hb]



theorem wiredThresholdSet_nonempty_q2 (d : Nat) (beta0 : Real) (hd : 2 <= d) :
    (BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n b)).Nonempty := by
  let pc := FK.fkPc d 2
  let p := (pc + 1) / 2
  let beta := -Real.log (1 - p)
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd (by norm_num)
  have hpc1 : pc < 1 := FK.fkPc_two_lt_one_of_two_le hd
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hpcp : pc < p := by dsimp [p]; linarith
  have hremain : 0 < 1 - p := by linarith
  have hremain1 : 1 - p < 1 := by linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    rw [neg_neg, Real.exp_log hremain]
    ring
  have hthetaP : 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : Real) < 2)
      (q := 2) :=
    FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num) hpcp
  have hthetaBeta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
    simpa only [hparam] using hthetaP
  exact wiredThresholdSet_nonempty_of_fkTheta_pos_q2
    d beta0 beta hbeta hthetaBeta



theorem wiredBeta1_nonneg_q2 (d : Nat) (beta0 : Real) (hd : 2 <= d) :
    0 <= wiredBeta1 d beta0 := by
  unfold wiredBeta1 BetaThresholdBound.beta1
  apply le_csInf (wiredThresholdSet_nonempty_q2 d beta0 hd)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n beta))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n beta) / Real.log (n : Real)
    rw [thresholdSig_of_nonpos d n hn 2 beta0 beta hbetaNeg.le]
  change 1 <= limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d 2 beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem wiredNormalizedTheta_tendsto_betaFKTheta_div
    (d : Nat) (beta0 beta : Real) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredNormalizedTheta d 2 beta0 n beta) atTop
      (nhds (betaFKTheta d beta / wiredSharpConstant d beta0)) := by
  have h := wiredThresholdTheta_tendsto_fkTheta_div_q2 d beta0 beta hbeta
  simpa [wiredThresholdTheta, not_le.mpr hbeta,
    betaFKTheta_eq d beta hbeta] using h



theorem betaFKTheta_difference_lower_q2
    (d : Nat) (beta0 beta' beta : Real) (hd : 2 <= d)
    (hcrit : wiredBeta1 d beta0 < beta') (hbeta : beta' <= beta)
    (hupper : beta <= beta0) :
    beta - beta' <=
      betaFKTheta d beta / wiredSharpConstant d beta0 -
        betaFKTheta d beta' / wiredSharpConstant d beta0 := by
  let f := wiredNormalizedTheta d 2 beta0
  let fp := wiredNormalizedThetaPrime d 2 beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := wiredBeta1_nonneg_q2 d beta0 hd
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : forall i x, x ∈ Set.Icc beta' beta ->
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / wiredSharpConstant d beta0 := by
        funext z
        simp [f, wiredNormalizedTheta, wiredOuterInnerTheta]
      rw [hconst]
      simpa [fp, wiredNormalizedThetaPrime, wiredOuterInnerThetaPrime,
        wiredOuterInnerTheta] using
        (hasDerivAt_const x (1 / wiredSharpConstant d beta0))
    · exact hasDerivAt_wiredNormalizedTheta d i
        (Nat.one_le_iff_ne_zero.mpr hi) 2 beta0 x (by norm_num)
        (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_nonneg d i 2 beta0 x (by norm_num)
      (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 < Sig i x := by
    intro i x hi hx
    exact normalizedSig_pos d i hi 2 beta0 x (by norm_num)
      (hbeta'pos.trans_le hx.1)
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Set.Icc beta' beta ->
      ((i : Real) / Sig i x) * f i x <= fp i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_differential d i hi 2 x beta0 (by norm_num)
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Set.Icc beta' beta ->
      Sig n beta' <= Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' <= Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        wiredNormalizedTheta_mono_beta d k 2 beta0 beta' x (by norm_num)
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : forall x, x ∈ Set.Icc beta' beta ->
      Sig 1 x <= 1 / wiredSharpConstant d beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, wiredNormalizedTheta,
      wiredOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (betaFKTheta d beta / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKTheta_div d beta0 beta hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (betaFKTheta d beta' / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKTheta_div d beta0 beta' hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n beta') := by
    funext n
    symm
    exact thresholdSig_of_pos d n 2 beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_isCobounded d 2 beta0 beta' (by norm_num) hbeta0pos.le
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_bddAbove d 2 beta0 beta' (by norm_num) hbeta0pos.le
  have hm1 : 1 <= limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (wiredThresholdSet_nonempty_q2 d beta0 hd)
      (fun hab n => thresholdSig_mono_beta d n 2 beta0 (by norm_num) hab)
      (fun x n hn => thresholdSig_pos d n (by omega) 2 beta0 x (by norm_num))
      (fun x => thresholdLogRatio_isCobounded d 2 beta0 x (by norm_num) hbeta0pos.le)
      (fun x => thresholdLogRatio_bddAbove d 2 beta0 x (by norm_num) hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (betaFKTheta d beta / wiredSharpConstant d beta0)
    (betaFKTheta d beta' / wiredSharpConstant d beta0)
    (1 / wiredSharpConstant d beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1




theorem betaFKTheta_meanField_lower_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hcrit : wiredBeta1 d beta0 < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - wiredBeta1 d beta0) <=
      betaFKTheta d beta := by
  have hc : 0 < wiredSharpConstant d beta0 := wiredSharpConstant_pos d beta0
  have hnormalized : beta - wiredBeta1 d beta0 <=
      betaFKTheta d beta / wiredSharpConstant d beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => betaFKTheta d x / wiredSharpConstant d beta0)
      (β₁ := wiredBeta1 d beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg (betaFKTheta_nonneg d beta') hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact betaFKTheta_difference_lower_q2 d beta0 beta' beta hd
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith



theorem wiredBeta1_le_of_betaFKTheta_pos_q2
    (d : Nat) (beta0 : Real) (hbeta0 : 0 < betaFKTheta d beta0) :
    wiredBeta1 d beta0 <= beta0 := by
  have hb0 : 0 < beta0 := by
    by_contra h
    have hz : betaFKTheta d beta0 = 0 := by
      simp only [betaFKTheta, dif_neg h]
    linarith
  have htheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta0 < 0)
        linarith : 0 < 1 - Real.exp (-beta0))
      (by linarith [Real.exp_pos (-beta0)] : 1 - Real.exp (-beta0) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
    simpa only [betaFKTheta_eq d beta0 hb0] using hbeta0
  unfold wiredBeta1 BetaThresholdBound.beta1
  exact csInf_le (wiredThresholdSet_bddBelow d 2 beta0)
    (wiredThresholdSet_mem_of_fkTheta_pos_q2 d beta0 beta0 hb0 htheta)




theorem betaFKTheta_eq_zero_below_wiredBeta1_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0)
    (hlt : beta < wiredBeta1 d beta0) :
    betaFKTheta d beta = 0 := by
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + wiredBeta1 d beta0) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < wiredBeta1 d beta0 := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidBeta0 : betaMid <= beta0 :=
      hmidUpper.le.trans (wiredBeta1_le_of_betaFKTheta_pos_q2 d beta0 hbeta0)
    obtain ⟨Q, hQ, hdecay⟩ :=
      wiredOuterInner_subcritical_decay_of_threshold
        d 2 delta betaMid beta0 (by norm_num) hmidBeta0 hdelta
        (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1] using hmidUpper)
    have hconv : Tendsto (fun n => wiredOuterInnerTheta d 2 beta n) atTop
        (nhds (betaFKTheta d beta)) := by
      simpa only [betaFKTheta_eq d beta hbeta] using
        wiredOuterInnerTheta_tendsto_fkTheta_q2 d beta hbeta
    have hzero := BetaCMatch.bcm_expBound_tendsto_zero 1 Q delta hQ hdelta
    have hle : betaFKTheta d beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn)
    exact le_antisymm hle (betaFKTheta_nonneg d beta)
  · simp [betaFKTheta, hbeta]



theorem betaFKTheta_pos_above_wiredBeta1_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0)
    (hlt : wiredBeta1 d beta0 < beta) :
    0 < betaFKTheta d beta := by
  by_cases hupper : beta <= beta0
  · have hmf := betaFKTheta_meanField_lower_q2
      d beta0 beta hd hlt hupper
    have hgap : 0 < wiredSharpConstant d beta0 *
        (beta - wiredBeta1 d beta0) := mul_pos (wiredSharpConstant_pos d beta0)
          (sub_pos.mpr hlt)
    exact hgap.trans_le hmf
  · exact hbeta0.trans_le (betaFKTheta_mono d (le_of_lt (lt_of_not_ge hupper)))



theorem betaCritical_eq_wiredBeta1_q2
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = wiredBeta1 d beta0 := by
  exact BetaCMatch.bcm_betaC_eq_threshold (betaFKTheta d) (wiredBeta1 d beta0)
    (fun beta hlt =>
      betaFKTheta_eq_zero_below_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt)
    (fun beta hlt =>
      betaFKTheta_pos_above_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt)



noncomputable def fkBetaCritical (d : Nat) : Real :=
  -Real.log (1 - FK.fkPc d 2)




theorem betaCritical_eq_fkBetaCritical_q2
    (d : Nat) (hd : 2 <= d) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = fkBetaCritical d := by
  let pc := FK.fkPc d 2
  let betaC := fkBetaCritical d
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd (by norm_num)
  have hpc1 : pc < 1 := FK.fkPc_two_lt_one_of_two_le hd
  have hremain : 0 < 1 - pc := by linarith
  have hremain1 : 1 - pc < 1 := by linarith
  have hbetaC : 0 < betaC := by
    dsimp [betaC, fkBetaCritical]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-betaC) = pc := by
    dsimp [betaC, fkBetaCritical]
    rw [neg_neg, Real.exp_log hremain]
    ring
  apply BetaCMatch.bcm_betaC_eq_threshold (betaFKTheta d) betaC
  · intro beta hbelow
    by_cases hbeta : 0 < beta
    · rw [betaFKTheta_eq d beta hbeta]
      have hp : 0 < 1 - Real.exp (-beta) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith
      have hp1 : 1 - Real.exp (-beta) < 1 := by
        linarith [Real.exp_pos (-beta)]
      have hexp : Real.exp (-betaC) < Real.exp (-beta) :=
        Real.exp_lt_exp.mpr (by linarith)
      apply FK.tzp_fkTheta_eq_zero_of_lt_pc hp hp1
      have hlt : 1 - Real.exp (-beta) < pc := by
        rw [← hparam]
        linarith
      simpa [pc] using hlt
    · simp [betaFKTheta, hbeta]
  · intro beta habove
    have hbeta : 0 < beta := hbetaC.trans habove
    rw [betaFKTheta_eq d beta hbeta]
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hexp : Real.exp (-beta) < Real.exp (-betaC) :=
      Real.exp_lt_exp.mpr (by linarith)
    apply FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num)
    have hgt : pc < 1 - Real.exp (-beta) := by
      rw [← hparam]
      linarith
    simpa [pc] using hgt




theorem wiredBeta1_eq_fkBetaCritical_q2
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0) :
    wiredBeta1 d beta0 = fkBetaCritical d :=
  (betaCritical_eq_wiredBeta1_q2 d beta0 hd hbeta0).symm.trans
    (betaCritical_eq_fkBetaCritical_q2 d hd)



noncomputable def fkCriticalBeta (d : Nat) : Real :=
  -Real.log (1 - FK.fkPc d 2)

theorem fkCriticalBeta_pos (d : Nat) (hd : 2 <= d) :
    0 < fkCriticalBeta d := by
  have hpc0 := FK.fkPc_pos_of_two_le hd (by norm_num : (1 : Real) <= 2)
  have hpc1 := FK.fkPc_two_lt_one_of_two_le hd
  unfold fkCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc1) (by linarith))

theorem fkCriticalBeta_param (d : Nat) (hd : 2 <= d) :
    1 - Real.exp (-fkCriticalBeta d) = FK.fkPc d 2 := by
  have hpc1 := FK.fkPc_two_lt_one_of_two_le hd
  unfold fkCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc1)]
  ring

theorem betaToP_lt_fkPc_of_lt_fkCriticalBeta
    (d : Nat) (hd : 2 <= d) {beta : Real}
    (hbeta : beta < fkCriticalBeta d) :
    1 - Real.exp (-beta) < FK.fkPc d 2 := by
  rw [← fkCriticalBeta_param d hd]
  have hexp : Real.exp (-fkCriticalBeta d) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem fkPc_lt_betaToP_of_fkCriticalBeta_lt
    (d : Nat) (hd : 2 <= d) {beta : Real}
    (hbeta : fkCriticalBeta d < beta) :
    FK.fkPc d 2 < 1 - Real.exp (-beta) := by
  rw [← fkCriticalBeta_param d hd]
  have hexp : Real.exp (-beta) < Real.exp (-fkCriticalBeta d) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith




theorem wiredBeta1_eq_fkCriticalBeta_q2_of_ge
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : fkCriticalBeta d <= beta0) :
    wiredBeta1 d beta0 = fkCriticalBeta d := by
  let betaC := fkCriticalBeta d
  let Sgf : Real -> Nat -> Real := fun b n =>
    IntegrationSubcritical.Sig
      (wiredThresholdTheta d 2 beta0) n b
  have hbetaCpos : 0 < betaC := fkCriticalBeta_pos d hd
  have hbeta0pos : 0 < beta0 := hbetaCpos.trans_le hbeta0
  have hne : (BetaThresholdBound.thresholdSet Sgf).Nonempty := by
    simpa [Sgf] using wiredThresholdSet_nonempty_q2 d beta0 hd
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using wiredThresholdSet_bddBelow d 2 beta0
  have hle : wiredBeta1 d beta0 <= betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have htheta : 0 < FK.fkTheta d hp hp1
        (by norm_num : (0 : Real) < 2) (q := 2) :=
      FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num)
        (fkPc_lt_betaToP_of_fkCriticalBeta_lt d hd hbetaCbeta)
    have hmem := wiredThresholdSet_mem_of_fkTheta_pos_q2
      d beta0 beta hbetapos htheta
    unfold wiredBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC <= wiredBeta1 d beta0 := by
    by_contra hnot
    have hlt : wiredBeta1 d beta0 < betaC := lt_of_not_ge hnot
    let beta := (wiredBeta1 d beta0 + betaC) / 2
    have hcrit : wiredBeta1 d beta0 < beta := by dsimp [beta]; linarith
    have hbetaC : beta < betaC := by dsimp [beta]; linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (wiredBeta1_nonneg_q2 d beta0 hd) hcrit
    have hmean := betaFKTheta_meanField_lower_q2
      d beta0 beta hd hcrit (hbetaC.le.trans hbeta0)
    have hthetaPos : 0 < betaFKTheta d beta := by
      have hc := wiredSharpConstant_pos d beta0
      have hgap : 0 < beta - wiredBeta1 d beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hzero : FK.fkTheta d hp hp1
        (by norm_num : (0 : Real) < 2) (q := 2) = 0 :=
      FK.tzp_fkTheta_eq_zero_of_lt_pc hp hp1
        (betaToP_lt_fkPc_of_lt_fkCriticalBeta d hd hbetaC)
    rw [betaFKTheta_eq d beta hbetapos, hzero] at hthetaPos
    exact (lt_irrefl 0 hthetaPos)
  exact le_antisymm hle hge

theorem wiredBeta1_eq_fkCriticalBeta_q2 (d : Nat) (hd : 2 <= d) :
    wiredBeta1 d (fkCriticalBeta d) = fkCriticalBeta d :=
  wiredBeta1_eq_fkCriticalBeta_q2_of_ge d (fkCriticalBeta d) hd le_rfl


theorem wiredOuterInner_exponential_decay_below_fkCriticalBeta_q2
    (d : Nat) (beta : Real) (hd : 2 <= d)
    (hbeta : 0 < beta) (hsub : beta < fkCriticalBeta d) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
      wiredOuterInnerTheta d 2 beta n <=
        Real.exp (-((n : Real) / Q *
          ((fkCriticalBeta d - beta) / 4))) := by
  let betaMid := (beta + fkCriticalBeta d) / 2
  let delta := (fkCriticalBeta d - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidPos : 0 < betaMid := by dsimp [betaMid]; linarith
  have hmidLe : betaMid <= fkCriticalBeta d := by dsimp [betaMid]; linarith
  have hmidThreshold : betaMid < wiredBeta1 d (fkCriticalBeta d) := by
    rw [wiredBeta1_eq_fkCriticalBeta_q2 d hd]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_of_threshold
      d 2 delta betaMid (fkCriticalBeta d) (by norm_num) hmidLe hdelta
      (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, mul_assoc] using hdecay n hn


theorem betaFKTheta_meanField_above_fkCriticalBeta_q2
    (d : Nat) (beta : Real) (hd : 2 <= d)
    (hsuper : fkCriticalBeta d < beta) :
    wiredSharpConstant d beta * (beta - fkCriticalBeta d) <=
      betaFKTheta d beta := by
  have hthreshold : wiredBeta1 d beta = fkCriticalBeta d :=
    wiredBeta1_eq_fkCriticalBeta_q2_of_ge d beta hd hsuper.le
  have hcrit : wiredBeta1 d beta < beta := by rwa [hthreshold]
  simpa [hthreshold] using
    betaFKTheta_meanField_lower_q2 d beta beta hd hcrit le_rfl

end WiredBoxCritical
end OSSS
end StatMech
