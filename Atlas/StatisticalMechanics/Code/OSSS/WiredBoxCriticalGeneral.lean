/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.WiredBoxCritical
import Code.IsingFK.PottsCriticalCorrespondence

open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace WiredBoxCriticalGeneral

open Filter
open WiredBoxSharpness WiredBoxCritical
open WiredBoxLocalized

noncomputable def wiredBeta1Q
    (d : Nat) (q beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b)



noncomputable def betaFKThetaQ
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q)
  else 0

theorem betaFKThetaQ_eq
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) (hbeta : 0 < beta) :
    betaFKThetaQ d q hq beta = FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
  simp only [betaFKThetaQ, dif_pos hbeta]

theorem betaFKThetaQ_nonneg
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) :
    0 <= betaFKThetaQ d q hq beta := by
  by_cases hbeta : 0 < beta
  · rw [betaFKThetaQ_eq d q hq beta hbeta]
    exact FK.fkTheta_nonneg d _ _ (zero_lt_one.trans_le hq) (q := q)
  · simp [betaFKThetaQ, hbeta]


theorem wiredBeta1Q_nonneg
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q) :
    0 <= wiredBeta1Q d q beta0 := by
  unfold wiredBeta1Q BetaThresholdBound.beta1
  apply le_csInf (wiredThresholdSet_nonempty d q beta0 hd hq)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta))
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
        (wiredThresholdTheta d q beta0) n beta) / Real.log (n : Real)
    rw [thresholdSig_of_nonpos d n hn q beta0 beta hbetaNeg.le]
  change 1 <= limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem wiredNormalizedTheta_tendsto_betaFKThetaQ_div
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredNormalizedTheta d q beta0 n beta) atTop
      (nhds (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)) := by
  have h := wiredThresholdTheta_tendsto_fkTheta_div
    d q beta0 beta hq hbeta
  simpa [wiredThresholdTheta, not_le.mpr hbeta,
    betaFKThetaQ_eq d q hq beta hbeta] using h


theorem betaFKThetaQ_difference_lower
    (d : Nat) (q beta0 beta' beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hcrit : wiredBeta1Q d q beta0 < beta') (hbeta : beta' <= beta)
    (hupper : beta <= beta0) :
    beta - beta' <=
      betaFKThetaQ d q hq beta / wiredSharpConstant d beta0 -
        betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0 := by
  let f := wiredNormalizedTheta d q beta0
  let fp := wiredNormalizedThetaPrime d q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := wiredBeta1Q_nonneg d q beta0 hd hq
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
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_nonneg d i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 < Sig i x := by
    intro i x hi hx
    exact normalizedSig_pos d i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Set.Icc beta' beta ->
      ((i : Real) / Sig i x) * f i x <= fp i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_differential d i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Set.Icc beta' beta ->
      Sig n beta' <= Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' <= Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        wiredNormalizedTheta_mono_beta d k q beta0 beta' x hq
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
      (nhds (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKThetaQ_div
        d q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKThetaQ_div
        d q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n beta') := by
    funext n
    symm
    exact thresholdSig_of_pos d n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_isCobounded d q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_bddAbove d q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 <= limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (wiredThresholdSet_nonempty d q beta0 hd hq)
      (fun hab n => thresholdSig_mono_beta d n q beta0 hq hab)
      (fun x n hn => thresholdSig_pos d n (by omega) q beta0 x hq)
      (fun x => thresholdLogRatio_isCobounded d q beta0 x hq hbeta0pos.le)
      (fun x => thresholdLogRatio_bddAbove d q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)
    (betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0)
    (1 / wiredSharpConstant d beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1


theorem betaFKThetaQ_meanField_lower
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hcrit : wiredBeta1Q d q beta0 < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - wiredBeta1Q d q beta0) <=
      betaFKThetaQ d q hq beta := by
  have hc : 0 < wiredSharpConstant d beta0 := wiredSharpConstant_pos d beta0
  have hnormalized : beta - wiredBeta1Q d q beta0 <=
      betaFKThetaQ d q hq beta / wiredSharpConstant d beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => betaFKThetaQ d q hq x / wiredSharpConstant d beta0)
      (β₁ := wiredBeta1Q d q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg (betaFKThetaQ_nonneg d q hq beta') hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact betaFKThetaQ_difference_lower d q beta0 beta' beta hd hq
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith

theorem betaFKThetaQ_mono
    (d : Nat) (q : Real) (hq : 1 <= q) : Monotone (betaFKThetaQ d q hq) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · rw [betaFKThetaQ_eq d q hq a ha, betaFKThetaQ_eq d q hq b hb]
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
      exact FK.fkgq_fkTheta_monotone_in_p hpa0 hpa1 hpb0 hpb1 hpab hq
    · rw [show betaFKThetaQ d q hq a = 0 by simp [betaFKThetaQ, ha]]
      exact betaFKThetaQ_nonneg d q hq b
  · have ha : ¬ 0 < a := fun h => hb (h.trans_le hab)
    simp [betaFKThetaQ, ha, hb]

theorem wiredBeta1Q_le_of_betaFKThetaQ_pos
    (d : Nat) (q beta0 : Real) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    wiredBeta1Q d q beta0 <= beta0 := by
  have hb0 : 0 < beta0 := by
    by_contra h
    have hz : betaFKThetaQ d q hq beta0 = 0 := by
      simp only [betaFKThetaQ, dif_neg h]
    linarith
  have htheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta0 < 0)
        linarith : 0 < 1 - Real.exp (-beta0))
      (by linarith [Real.exp_pos (-beta0)] : 1 - Real.exp (-beta0) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
    simpa only [betaFKThetaQ_eq d q hq beta0 hb0] using hbeta0
  unfold wiredBeta1Q BetaThresholdBound.beta1
  exact csInf_le (wiredThresholdSet_bddBelow d q beta0)
    (wiredThresholdSet_mem_of_fkTheta_pos d q beta0 beta0 hq hb0 htheta)

theorem betaFKThetaQ_eq_zero_below_wiredBeta1
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hlt : beta < wiredBeta1Q d q beta0) :
    betaFKThetaQ d q hq beta = 0 := by
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + wiredBeta1Q d q beta0) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < wiredBeta1Q d q beta0 := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidBeta0 : betaMid <= beta0 :=
      hmidUpper.le.trans
        (wiredBeta1Q_le_of_betaFKThetaQ_pos d q beta0 hq hbeta0)
    obtain ⟨Q, hQ, hdecay⟩ :=
      wiredOuterInner_subcritical_decay_of_threshold
        d q delta betaMid beta0 hq hmidBeta0 hdelta
        (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1Q] using hmidUpper)
    have hconv : Tendsto (fun n => wiredOuterInnerTheta d q beta n) atTop
        (nhds (betaFKThetaQ d q hq beta)) := by
      simpa only [betaFKThetaQ_eq d q hq beta hbeta] using
        wiredOuterInnerTheta_tendsto_fkTheta d q beta hq hbeta
    have hzero := BetaCMatch.bcm_expBound_tendsto_zero 1 Q delta hQ hdelta
    have hle : betaFKThetaQ d q hq beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn)
    exact le_antisymm hle (betaFKThetaQ_nonneg d q hq beta)
  · simp [betaFKThetaQ, hbeta]

theorem betaFKThetaQ_pos_above_wiredBeta1
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hlt : wiredBeta1Q d q beta0 < beta) :
    0 < betaFKThetaQ d q hq beta := by
  by_cases hupper : beta <= beta0
  · have hmf := betaFKThetaQ_meanField_lower
      d q beta0 beta hd hq hlt hupper
    have hgap : 0 < wiredSharpConstant d beta0 *
        (beta - wiredBeta1Q d q beta0) :=
      mul_pos (wiredSharpConstant_pos d beta0) (sub_pos.mpr hlt)
    exact hgap.trans_le hmf
  · exact hbeta0.trans_le
      (betaFKThetaQ_mono d q hq (le_of_lt (lt_of_not_ge hupper)))

theorem betaCriticalQ_eq_wiredBeta1Q
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) =
      wiredBeta1Q d q beta0 := by
  exact BetaCMatch.bcm_betaC_eq_threshold
    (betaFKThetaQ d q hq) (wiredBeta1Q d q beta0)
    (fun beta hlt => betaFKThetaQ_eq_zero_below_wiredBeta1
      d q beta0 beta hd hq hbeta0 hlt)
    (fun beta hlt => betaFKThetaQ_pos_above_wiredBeta1
      d q beta0 beta hd hq hbeta0 hlt)

noncomputable def fkBetaCriticalQ (d : Nat) (q : Real) : Real :=
  -Real.log (1 - FK.fkPc d q)

theorem betaCriticalQ_eq_fkBetaCriticalQ
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) =
      fkBetaCriticalQ d q := by
  let pc := FK.fkPc d q
  let betaC := fkBetaCriticalQ d q
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd hq
  have hpc1 : pc < 1 := FK.fkPc_lt_one_of_two_le hd hq
  have hremain : 0 < 1 - pc := by linarith
  have hremain1 : 1 - pc < 1 := by linarith
  have hbetaC : 0 < betaC := by
    dsimp [betaC, fkBetaCriticalQ]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-betaC) = pc := by
    dsimp [betaC, fkBetaCriticalQ]
    rw [neg_neg, Real.exp_log hremain]
    ring
  apply BetaCMatch.bcm_betaC_eq_threshold (betaFKThetaQ d q hq) betaC
  · intro beta hbelow
    by_cases hbeta : 0 < beta
    · rw [betaFKThetaQ_eq d q hq beta hbeta]
      have hp : 0 < 1 - Real.exp (-beta) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith
      have hp1 : 1 - Real.exp (-beta) < 1 := by
        linarith [Real.exp_pos (-beta)]
      have hexp : Real.exp (-betaC) < Real.exp (-beta) :=
        Real.exp_lt_exp.mpr (by linarith)
      apply FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq
      have hlt : 1 - Real.exp (-beta) < pc := by
        rw [← hparam]
        linarith
      simpa [pc] using hlt
    · simp [betaFKThetaQ, hbeta]
  · intro beta habove
    have hbeta : 0 < beta := hbetaC.trans habove
    rw [betaFKThetaQ_eq d q hq beta hbeta]
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hexp : Real.exp (-beta) < Real.exp (-betaC) :=
      Real.exp_lt_exp.mpr (by linarith)
    apply FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans_le hq)
    have hgt : pc < 1 - Real.exp (-beta) := by
      rw [← hparam]
      linarith
    simpa [pc] using hgt

theorem wiredBeta1Q_eq_fkBetaCriticalQ
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    wiredBeta1Q d q beta0 = fkBetaCriticalQ d q :=
  (betaCriticalQ_eq_wiredBeta1Q d q beta0 hd hq hbeta0).symm.trans
    (betaCriticalQ_eq_fkBetaCriticalQ d q hd hq)


theorem betaFKThetaQ_meanField_above_fkBetaCriticalQ
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hcrit : fkBetaCriticalQ d q < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - fkBetaCriticalQ d q) <=
      betaFKThetaQ d q hq beta := by
  have hthreshold := wiredBeta1Q_eq_fkBetaCriticalQ d q beta0 hd hq hbeta0
  have hcrit' : wiredBeta1Q d q beta0 < beta := by
    rw [hthreshold]
    exact hcrit
  have h := betaFKThetaQ_meanField_lower
    d q beta0 beta hd hq hcrit' hupper
  rwa [hthreshold] at h



theorem wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hbeta : 0 < beta) (hcrit : beta < fkBetaCriticalQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      wiredOuterInnerTheta d q beta n <= Real.exp (-((n : Real) / Q)) := by
  let betaMid := (beta + fkBetaCriticalQ d q) / 2
  let delta := (betaMid - beta) / 2
  have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
  have hmidUpper : betaMid < fkBetaCriticalQ d q := by
    dsimp [betaMid]
    linarith
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [delta, betaMid]
    ring
  have hthreshold := wiredBeta1Q_eq_fkBetaCriticalQ d q beta0 hd hq hbeta0
  have hmidBeta0 : betaMid <= beta0 := by
    have hbeta1le := wiredBeta1Q_le_of_betaFKThetaQ_pos d q beta0 hq hbeta0
    rw [hthreshold] at hbeta1le
    exact hmidUpper.le.trans hbeta1le
  obtain ⟨Q, hQ, hdecay⟩ := wiredOuterInner_subcritical_decay_of_threshold
    d q delta betaMid beta0 hq hmidBeta0 hdelta
      (by rw [hleft]; exact hbeta) (by
        change betaMid < wiredBeta1Q d q beta0
        rw [hthreshold]
        exact hmidUpper)
  refine ⟨Q / delta, div_pos hQ hdelta, ?_⟩
  intro n hn
  have h := hdecay n hn
  rw [hleft] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def fkCriticalBetaQ (d : Nat) (q : Real) : Real :=
  -Real.log (1 - FK.fkPc d q)

theorem fkCriticalBetaQ_pos
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    0 < fkCriticalBetaQ d q := by
  have hpc0 := FK.fkPc_pos_of_two_le hd hq
  have hpc1 := FK.fkPc_lt_one_of_two_le hd hq
  unfold fkCriticalBetaQ
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc1) (by linarith))

theorem fkCriticalBetaQ_param
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    1 - Real.exp (-fkCriticalBetaQ d q) = FK.fkPc d q := by
  have hpc1 := FK.fkPc_lt_one_of_two_le hd hq
  unfold fkCriticalBetaQ
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc1)]
  ring

theorem betaToP_lt_fkPc_of_lt_fkCriticalBetaQ
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) {beta : Real}
    (hbeta : beta < fkCriticalBetaQ d q) :
    1 - Real.exp (-beta) < FK.fkPc d q := by
  rw [← fkCriticalBetaQ_param d q hd hq]
  have hexp : Real.exp (-fkCriticalBetaQ d q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem fkPc_lt_betaToP_of_fkCriticalBetaQ_lt
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) {beta : Real}
    (hbeta : fkCriticalBetaQ d q < beta) :
    FK.fkPc d q < 1 - Real.exp (-beta) := by
  rw [← fkCriticalBetaQ_param d q hd hq]
  have hexp : Real.exp (-beta) < Real.exp (-fkCriticalBetaQ d q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith



theorem wiredBeta1Q_eq_fkCriticalBetaQ_of_ge
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : fkCriticalBetaQ d q <= beta0) :
    wiredBeta1Q d q beta0 = fkCriticalBetaQ d q := by
  let betaC := fkCriticalBetaQ d q
  let Sgf : Real -> Nat -> Real := fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b
  have hbetaCpos : 0 < betaC := fkCriticalBetaQ_pos d q hd hq
  have hbeta0pos : 0 < beta0 := hbetaCpos.trans_le hbeta0
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using wiredThresholdSet_bddBelow d q beta0
  have hle : wiredBeta1Q d q beta0 <= betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have htheta : 0 < FK.fkTheta d hp hp1
        (zero_lt_one.trans_le hq) (q := q) :=
      FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans_le hq)
        (fkPc_lt_betaToP_of_fkCriticalBetaQ_lt d q hd hq hbetaCbeta)
    have hmem := wiredThresholdSet_mem_of_fkTheta_pos
      d q beta0 beta hq hbetapos htheta
    unfold wiredBeta1Q BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC <= wiredBeta1Q d q beta0 := by
    by_contra hnot
    have hlt : wiredBeta1Q d q beta0 < betaC := lt_of_not_ge hnot
    let beta := (wiredBeta1Q d q beta0 + betaC) / 2
    have hcrit : wiredBeta1Q d q beta0 < beta := by dsimp [beta]; linarith
    have hbetaC : beta < betaC := by dsimp [beta]; linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (wiredBeta1Q_nonneg d q beta0 hd hq) hcrit
    have hmean := betaFKThetaQ_meanField_lower
      d q beta0 beta hd hq hcrit (hbetaC.le.trans hbeta0)
    have hthetaPos : 0 < betaFKThetaQ d q hq beta := by
      have hc := wiredSharpConstant_pos d beta0
      have hgap : 0 < beta - wiredBeta1Q d q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hzero : FK.fkTheta d hp hp1
        (zero_lt_one.trans_le hq) (q := q) = 0 :=
      FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq
        (betaToP_lt_fkPc_of_lt_fkCriticalBetaQ d q hd hq hbetaC)
    rw [betaFKThetaQ_eq d q hq beta hbetapos, hzero] at hthetaPos
    exact (lt_irrefl 0 hthetaPos)
  exact le_antisymm hle hge


theorem wiredOuterInner_exponential_decay_below_fkCriticalBetaQ
    (d : Nat) (q beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta : 0 < beta) (hsub : beta < fkCriticalBetaQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
      wiredOuterInnerTheta d q beta n <=
        Real.exp (-((n : Real) / Q *
          ((fkCriticalBetaQ d q - beta) / 4))) := by
  let betaC := fkCriticalBetaQ d q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid <= betaC := by dsimp [betaMid]; linarith
  have hthreshold : wiredBeta1Q d q betaC = betaC :=
    wiredBeta1Q_eq_fkCriticalBetaQ_of_ge d q betaC hd hq le_rfl
  have hmidThreshold : betaMid < wiredBeta1Q d q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_of_threshold
      d q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [wiredBeta1Q] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn


theorem betaFKThetaQ_meanField_above_fkCriticalBetaQ
    (d : Nat) (q beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hsuper : fkCriticalBetaQ d q < beta) :
    wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <=
      betaFKThetaQ d q hq beta := by
  have hthreshold : wiredBeta1Q d q beta = fkCriticalBetaQ d q :=
    wiredBeta1Q_eq_fkCriticalBetaQ_of_ge d q beta hd hq hsuper.le
  have hcrit : wiredBeta1Q d q beta < beta := by rwa [hthreshold]
  simpa [hthreshold] using
    betaFKThetaQ_meanField_lower d q beta beta hd hq hcrit le_rfl





theorem fkSharpness_homogeneous
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    (forall beta, fkCriticalBetaQ d q <= beta ->
      wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <=
        betaFKThetaQ d q hq beta) ∧
    (forall beta, 0 < beta -> beta < fkCriticalBetaQ d q ->
      ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
        wiredOuterInnerTheta d q beta n <=
          Real.exp (-((n : Real) / Q *
            ((fkCriticalBetaQ d q - beta) / 4)))) := by
  constructor
  · intro beta hbeta
    rcases hbeta.eq_or_lt with rfl | hsuper
    · simpa using betaFKThetaQ_nonneg d q hq (fkCriticalBetaQ d q)
    · exact betaFKThetaQ_meanField_above_fkCriticalBetaQ
        d q beta hd hq hsuper
  · intro beta hbeta hsub
    exact wiredOuterInner_exponential_decay_below_fkCriticalBetaQ
      d q beta hd hq hbeta hsub

end WiredBoxCriticalGeneral
end OSSS
end StatMech
