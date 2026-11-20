/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.WiredBoxOffCentre
import Code.OSSS.IntegrationSubcriticalAssembly
import Code.OSSS.BetaThresholdBound
import Code.OSSS.LogCesaroLimit

open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace WiredBoxSharpness

open Lattice FK
open WiredBoxLocalized WiredBoxOffCentre
open MeasureTheory


noncomputable def wiredOuterInnerThetaPrime
    (d n : Nat) (q beta : Real) : Real :=
  deriv (fun b => wiredOuterInnerTheta d q b n) beta



noncomputable def wiredSharpConstant (d : Nat) (beta0 : Real) : Real :=
  Real.exp (-beta0) ^ (2 * d) / 8


noncomputable def wiredNormalizedTheta
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  wiredOuterInnerTheta d q beta n / wiredSharpConstant d beta0

noncomputable def wiredNormalizedThetaPrime
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  wiredOuterInnerThetaPrime d n q beta / wiredSharpConstant d beta0



noncomputable def wiredThresholdTheta
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / wiredSharpConstant d beta0 else 0
  else wiredNormalizedTheta d q beta0 n beta

theorem wiredSharpConstant_pos (d : Nat) (beta0 : Real) :
    0 < wiredSharpConstant d beta0 := by
  unfold wiredSharpConstant
  positivity

theorem wiredSharpConstant_le_one (d : Nat) (beta0 : Real)
    (hbeta0 : 0 <= beta0) : wiredSharpConstant d beta0 <= 1 := by
  have he0 : 0 <= Real.exp (-beta0) := (Real.exp_pos _).le
  have he1 : Real.exp (-beta0) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hp := pow_le_one₀ he0 he1 (n := 2 * d)
  unfold wiredSharpConstant
  nlinarith

theorem one_le_inv_wiredSharpConstant (d : Nat) (beta0 : Real)
    (hbeta0 : 0 <= beta0) : 1 <= 1 / wiredSharpConstant d beta0 :=
  one_le_one_div (wiredSharpConstant_pos d beta0)
    (wiredSharpConstant_le_one d beta0 hbeta0)



theorem wiredOuterInnerTheta_eq_activeBCMean
    (d n : Nat) (hn : 1 <= n) (q beta : Real) :
    wiredOuterInnerTheta d q beta n =
      activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) beta) q (innerCrossInd d n) := by
  rw [wiredOuterInnerTheta, if_neg (by omega)]
  rfl



theorem hasDerivAt_wiredOuterInnerTheta
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (fun b => wiredOuterInnerTheta d q b n)
      (wiredOuterInnerThetaPrime d n q beta) beta := by
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have h := hasDerivAt_activeBCMean_beta_sum
    (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    hJ hbeta (zero_lt_one.trans_le hq) (innerCrossInd d n)
  have heq : (fun b => wiredOuterInnerTheta d q b n) =
      (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q (innerCrossInd d n)) := by
    funext b
    exact wiredOuterInnerTheta_eq_activeBCMean d n hn q b
  rw [heq]
  unfold wiredOuterInnerThetaPrime
  rw [heq]
  exact h.congr_deriv h.deriv.symm



theorem wiredOuterInnerSig_eq_integrationSig
    (d n : Nat) (q beta : Real) :
    wiredOuterInnerSig d n q beta =
      IntegrationSubcritical.Sig
        (fun k b => wiredOuterInnerTheta d q b k) n beta := by
  rfl

theorem normalizedSig_eq
    (d n : Nat) (q beta0 beta : Real) :
    IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta =
      wiredOuterInnerSig d n q beta / wiredSharpConstant d beta0 := by
  unfold IntegrationSubcritical.Sig wiredNormalizedTheta wiredOuterInnerSig
  rw [Finset.sum_div]

theorem wiredThresholdTheta_of_pos
    (d n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    wiredThresholdTheta d q beta0 n beta =
      wiredNormalizedTheta d q beta0 n beta := by
  simp [wiredThresholdTheta, not_le.mpr hbeta]

theorem thresholdSig_of_pos
    (d n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta =
      IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta := by
  unfold IntegrationSubcritical.Sig
  apply Finset.sum_congr rfl
  intro k hk
  exact wiredThresholdTheta_of_pos d k q beta0 beta hbeta

theorem thresholdSig_of_nonpos
    (d n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hbeta : beta <= 0) :
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta =
      1 / wiredSharpConstant d beta0 := by
  unfold IntegrationSubcritical.Sig wiredThresholdTheta
  simp only [if_pos hbeta]
  rw [Finset.sum_eq_single 0]
  · simp [(wiredSharpConstant_pos d beta0).ne']
  · intro k hk hk0
    simp [hk0]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hn)).elim


theorem wiredThresholdSet_bddBelow (d : Nat) (q beta0 : Real) :
    BddBelow (BetaThresholdBound.thresholdSet
      (fun b n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n b)) := by
  refine ⟨0, ?_⟩
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Filter.Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun n : Nat => Real.log (n : Real))
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Filter.Tendsto (fun n : Nat =>
        Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real))
        Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n beta) / Real.log (n : Real)
    rw [thresholdSig_of_nonpos d n hn q beta0 beta hbetaNeg.le]
  have hlimsup := htend.limsup_eq
  change 1 <= Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta)) Filter.atTop at hmem
  rw [hlimsup] at hmem
  linarith
































































































































































































































































































































theorem wiredOuterInnerTheta_differential
    (d n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    wiredSharpConstant d beta0 *
        (((n : Real) / wiredOuterInnerSig d n q beta) *
          wiredOuterInnerTheta d q beta n) <=
      wiredOuterInnerThetaPrime d n q beta := by
  have hmain := wired_outer_inner_differential_uniform_box
    d n hn q beta beta0 hq hbeta hbeta0
  have hSig := wiredOuterInnerSig_pos d n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  rw [wiredOuterInnerTheta_eq_activeBCMean d n hn q beta]
  unfold wiredOuterInnerThetaPrime wiredSharpConstant
  rw [show deriv (fun b => wiredOuterInnerTheta d q b n) beta =
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q (innerCrossInd d n)) beta by
    congr 1
    funext b
    exact wiredOuterInnerTheta_eq_activeBCMean d n hn q b]
  calc
    (Real.exp (-beta0) ^ (2 * d) / 8) *
          ((n : Real) / wiredOuterInnerSig d n q beta *
            activeBCMean (boxGraph d (2 * n))
              (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
              (betaParams (fun _ => 1) beta) q (innerCrossInd d n)) =
        Real.exp (-beta0) ^ (2 * d) *
          (activeBCMean (boxGraph d (2 * n))
              (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
              (betaParams (fun _ => 1) beta) q (innerCrossInd d n) /
            (8 * wiredOuterInnerSig d n q beta / (n : Real))) := by
      field_simp
      <;> ring
    _ <= _ := hmain


theorem hasDerivAt_wiredNormalizedTheta
    (d n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (wiredNormalizedTheta d q beta0 n)
      (wiredNormalizedThetaPrime d q beta0 n beta) beta := by
  have h := hasDerivAt_wiredOuterInnerTheta d n hn q beta hq hbeta
  simpa [wiredNormalizedTheta, wiredNormalizedThetaPrime] using
    h.div_const (wiredSharpConstant d beta0)



theorem wiredNormalizedTheta_differential
    (d n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (((n : Real) /
        IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta) *
      wiredNormalizedTheta d q beta0 n beta) <=
        wiredNormalizedThetaPrime d q beta0 n beta := by
  have hc := wiredSharpConstant_pos d beta0
  have hSig := wiredOuterInnerSig_pos d n hn q beta hq hbeta
  have hmain := wiredOuterInnerTheta_differential
    d n hn q beta beta0 hq hbeta hbeta0
  rw [normalizedSig_eq]
  unfold wiredNormalizedTheta wiredNormalizedThetaPrime
  rw [le_div_iff₀ hc]
  convert hmain using 1 <;> field_simp <;> ring

theorem wiredOuterInnerTheta_le_one
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    wiredOuterInnerTheta d q beta n <= 1 := by
  by_cases hn0 : n = 0
  · simp [wiredOuterInnerTheta, hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let mu := activeBCProb (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    (betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0
  rw [wiredOuterInnerTheta_eq_activeBCMean d n hn q beta]
  calc
    activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) beta) q (innerCrossInd d n) <=
      Lindeberg.mean mu (fun _ => (1 : Real)) := by
        unfold activeBCMean Lindeberg.mean mu
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        unfold innerCrossInd AdaptiveCovLowerGeom.crossIndG
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hmu1 1

theorem wiredNormalizedTheta_nonneg
    (d n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= wiredNormalizedTheta d q beta0 n beta := by
  exact div_nonneg
    (wiredOuterInnerTheta_nonneg d q beta hq hbeta n)
    (wiredSharpConstant_pos d beta0).le

theorem wiredNormalizedTheta_le_invConstant
    (d n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    wiredNormalizedTheta d q beta0 n beta <= 1 / wiredSharpConstant d beta0 := by
  unfold wiredNormalizedTheta
  exact div_le_div_of_nonneg_right
    (wiredOuterInnerTheta_le_one d n q beta hq hbeta)
    (wiredSharpConstant_pos d beta0).le

theorem normalizedSig_pos
    (d n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < IntegrationSubcritical.Sig
      (wiredNormalizedTheta d q beta0) n beta := by
  rw [normalizedSig_eq]
  exact div_pos (wiredOuterInnerSig_pos d n hn q beta hq hbeta)
    (wiredSharpConstant_pos d beta0)

theorem wiredOuterInnerThetaPrime_nonneg
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= wiredOuterInnerThetaPrime d n q beta := by
  have hlog := wired_outer_inner_differential_sharp_uniform
    d n hn q beta hq hbeta
  have htheta0 := wiredOuterInnerTheta_nonneg d q beta hq hbeta n
  have htheta1 := wiredOuterInnerTheta_le_one d n q beta hq hbeta
  have hSig := wiredOuterInnerSig_pos d n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < 8 * wiredOuterInnerSig d n q beta / (n : Real) := by
    positivity
  have hnum : 0 <= wiredOuterInnerTheta d q beta n *
      (1 - wiredOuterInnerTheta d q beta n) :=
    mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hnonneg : 0 <= wiredOuterInnerTheta d q beta n *
      (1 - wiredOuterInnerTheta d q beta n) /
        (8 * wiredOuterInnerSig d n q beta / (n : Real)) :=
    div_nonneg hnum hD.le
  have hfun : (fun b => wiredOuterInnerTheta d q b n) =
      (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q (innerCrossInd d n)) := by
    funext b
    exact wiredOuterInnerTheta_eq_activeBCMean d n hn q b
  unfold wiredOuterInnerThetaPrime
  rw [hfun]
  exact hnonneg.trans (by
    simpa [wiredOuterInnerTheta_eq_activeBCMean d n hn q beta] using hlog)

theorem wiredNormalizedThetaPrime_nonneg
    (d n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= wiredNormalizedThetaPrime d q beta0 n beta := by
  unfold wiredNormalizedThetaPrime
  exact div_nonneg (wiredOuterInnerThetaPrime_nonneg d n hn q beta hq hbeta)
    (wiredSharpConstant_pos d beta0).le



theorem wiredNormalizedTheta_mono_beta
    (d n : Nat) (q beta0 y x : Real) (hq : 1 <= q)
    (hy : 0 < y) (hyx : y <= x) :
    wiredNormalizedTheta d q beta0 n y <=
      wiredNormalizedTheta d q beta0 n x := by
  by_cases hn0 : n = 0
  · subst n
    simp [wiredNormalizedTheta, wiredOuterInnerTheta]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let f := wiredNormalizedTheta d q beta0 n
  let f' := wiredNormalizedThetaPrime d q beta0 n
  have hd : ∀ z, z ∈ Set.Icc y x → HasDerivAt f (f' z) z := by
    intro z hz
    exact hasDerivAt_wiredNormalizedTheta d n hn q beta0 z hq
      (hy.trans_le hz.1)
  have hmono : MonotoneOn f (Set.Icc y x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y x)
    · intro z hz
      exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (Set.mem_Icc_of_Ioo hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (Set.mem_Icc_of_Ioo hz)).deriv]
      exact wiredNormalizedThetaPrime_nonneg d n hn q beta0 z hq
        (hy.trans hz.1)
  exact hmono (Set.left_mem_Icc.mpr hyx) (Set.right_mem_Icc.mpr hyx) hyx

theorem wiredThresholdTheta_nonneg
    (d n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    0 <= wiredThresholdTheta d q beta0 n beta := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [wiredThresholdTheta, if_pos hbeta, if_pos hn0]
      exact (div_pos one_pos (wiredSharpConstant_pos d beta0)).le
    · rw [wiredThresholdTheta, if_pos hbeta, if_neg hn0]
  · rw [wiredThresholdTheta_of_pos d n q beta0 beta (lt_of_not_ge hbeta)]
    exact wiredNormalizedTheta_nonneg d n q beta0 beta hq (lt_of_not_ge hbeta)

theorem wiredThresholdTheta_le_invConstant
    (d n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    wiredThresholdTheta d q beta0 n beta <= 1 / wiredSharpConstant d beta0 := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [wiredThresholdTheta, if_pos hbeta, if_pos hn0]
    · rw [wiredThresholdTheta, if_pos hbeta, if_neg hn0]
      exact (div_pos one_pos (wiredSharpConstant_pos d beta0)).le
  · rw [wiredThresholdTheta_of_pos d n q beta0 beta (lt_of_not_ge hbeta)]
    exact wiredNormalizedTheta_le_invConstant d n q beta0 beta hq (lt_of_not_ge hbeta)

theorem wiredThresholdTheta_mono_beta
    (d n : Nat) (q beta0 a b : Real) (hq : 1 <= q) (hab : a <= b) :
    wiredThresholdTheta d q beta0 n a <=
      wiredThresholdTheta d q beta0 n b := by
  by_cases hb : b <= 0
  · have ha : a <= 0 := hab.trans hb
    simp [wiredThresholdTheta, ha, hb]
  by_cases ha : a <= 0
  · by_cases hn0 : n = 0
    · subst n
      simp [wiredThresholdTheta, ha, hb, wiredNormalizedTheta,
        wiredOuterInnerTheta]
    · rw [wiredThresholdTheta, if_pos ha, if_neg hn0,
        wiredThresholdTheta, if_neg hb]
      exact wiredNormalizedTheta_nonneg d n q beta0 b hq (lt_of_not_ge hb)
  · rw [wiredThresholdTheta_of_pos d n q beta0 a (lt_of_not_ge ha),
      wiredThresholdTheta_of_pos d n q beta0 b (lt_of_not_ge hb)]
    exact wiredNormalizedTheta_mono_beta d n q beta0 a b hq
      (lt_of_not_ge ha) hab

theorem thresholdSig_mono_beta
    (d n : Nat) (q beta0 : Real) (hq : 1 <= q)
    {a b : Real} (hab : a <= b) :
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n a <=
      IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b := by
  unfold IntegrationSubcritical.Sig
  exact Finset.sum_le_sum (fun k _ =>
    wiredThresholdTheta_mono_beta d k q beta0 a b hq hab)

theorem thresholdSig_pos
    (d n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hq : 1 <= q) :
    0 < IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta := by
  have hzero : wiredThresholdTheta d q beta0 0 beta =
      1 / wiredSharpConstant d beta0 := by
    by_cases hbeta : beta <= 0
    · simp [wiredThresholdTheta, hbeta]
    · simp [wiredThresholdTheta, hbeta, wiredNormalizedTheta,
        wiredOuterInnerTheta]
  have hsum : wiredThresholdTheta d q beta0 0 beta <=
      IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta := by
    unfold IntegrationSubcritical.Sig
    apply Finset.single_le_sum
      (fun k _ => wiredThresholdTheta_nonneg d k q beta0 beta hq)
    simpa using hn
  rw [hzero] at hsum
  exact (div_pos zero_lt_one (wiredSharpConstant_pos d beta0)).trans_le hsum

theorem thresholdSig_le_linear
    (d n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta <=
      (1 / wiredSharpConstant d beta0) * (n : Real) := by
  unfold IntegrationSubcritical.Sig
  calc
    ∑ k ∈ Finset.range n, wiredThresholdTheta d q beta0 k beta <=
        ∑ _k ∈ Finset.range n, (1 / wiredSharpConstant d beta0) := by
      exact Finset.sum_le_sum (fun k _ =>
        wiredThresholdTheta_le_invConstant d k q beta0 beta hq)
    _ = (1 / wiredSharpConstant d beta0) * (n : Real) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem thresholdLogRatio_bddAbove
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta0 : 0 <= beta0) :
    Filter.IsBoundedUnder (fun x y : Real => x <= y) Filter.atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n beta)) := by
  exact BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta)
    (1 / wiredSharpConstant d beta0)
    (one_le_inv_wiredSharpConstant d beta0 hbeta0)
    (fun n hn => thresholdSig_pos d n (by omega) q beta0 beta hq)
    (fun n => thresholdSig_le_linear d n q beta0 beta hq)

theorem thresholdLogRatio_isCobounded
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta0 : 0 <= beta0) :
    Filter.IsCoboundedUnder (fun x y : Real => x <= y) Filter.atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n beta)) := by
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta))
    (x := 0) Filter.atTop ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig1 : 1 <= IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta := by
    have hzero : 1 <= wiredThresholdTheta d q beta0 0 beta := by
      have hM := one_le_inv_wiredSharpConstant d beta0 hbeta0
      by_cases hbeta : beta <= 0
      · simpa [wiredThresholdTheta, hbeta] using hM
      · rw [wiredThresholdTheta_of_pos d 0 q beta0 beta (lt_of_not_ge hbeta)]
        simpa [wiredNormalizedTheta, wiredOuterInnerTheta] using hM
    exact hzero.trans (by
      unfold IntegrationSubcritical.Sig
      apply Finset.single_le_sum
        (fun k _ => wiredThresholdTheta_nonneg d k q beta0 beta hq)
      exact Finset.mem_range.mpr (by omega))
  unfold BetaThresholdBound.logRatio
  exact div_nonneg (Real.log_nonneg hsig1) hlogn.le

theorem wiredThresholdSet_upward
    (d : Nat) (q beta0 : Real) (hq : 1 <= q) (hbeta0 : 0 <= beta0)
    {a b : Real} (hab : a <= b)
    (ha : a ∈ BetaThresholdBound.thresholdSet
      (fun x n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n x)) :
    b ∈ BetaThresholdBound.thresholdSet
      (fun x n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n x) := by
  exact LogCesaroLimit.thresholdSet_upward
    (fun hxy n => thresholdSig_mono_beta d n q beta0 hq hxy)
    (fun x n hn => thresholdSig_pos d n (by omega) q beta0 x hq)
    (fun x => thresholdLogRatio_isCobounded d q beta0 x hq hbeta0)
    (fun x => thresholdLogRatio_bddAbove d q beta0 x hq hbeta0)
    hab ha



theorem logRatio_sum_tendsto_one_of_tendsto_pos_active
    (u : Nat -> Real) (L : Real) (hL : 0 < L)
    (hu : Filter.Tendsto u Filter.atTop (nhds L)) :
    Filter.Tendsto
      (BetaThresholdBound.logRatio (fun n => ∑ k ∈ Finset.range n, u k))
      Filter.atTop (nhds 1) :=
  LogCesaroLimit.logRatio_partialSum_tendsto_one hu hL

theorem thresholdSet_mem_of_tendsto_pos_active
    (f : Nat -> Real) (L : Real) (hL : 0 < L)
    (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
    (0 : Real) ∈ BetaThresholdBound.thresholdSet
      (fun _ n => ∑ k ∈ Finset.range n, f k) := by
  have hratio := logRatio_sum_tendsto_one_of_tendsto_pos_active f L hL hf
  change 1 <= Filter.limsup
    (BetaThresholdBound.logRatio (fun n => ∑ k ∈ Finset.range n, f k))
      Filter.atTop
  rw [hratio.limsup_eq]





theorem wiredOuterInner_subcritical_decay_of_threshold
    (d : Nat) (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0)
    (hdelta : 0 < delta) (hleft : 0 < beta - 2 * delta)
    (hlt : beta < BetaThresholdBound.beta1
      (fun b n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n b)) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      wiredOuterInnerTheta d q (beta - 2 * delta) n <=
        Real.exp (-(((n : Real) / Q) * delta)) := by
  let f := wiredThresholdTheta d q beta0
  let f' := wiredNormalizedThetaPrime d q beta0
  let c := wiredSharpConstant d beta0
  let M := 1 / c
  let C := max 1 M
  have hc : 0 < c := wiredSharpConstant_pos d beta0
  have hM : 0 <= M := by unfold M; positivity
  have hC : 1 <= C := le_max_left _ _
  have hMC : M <= C := le_max_right _ _
  have hinterval : ∀ x ∈ Set.Icc (beta - 2 * delta) beta, 0 < x := by
    intro x hx
    exact hleft.trans_le hx.1
  have hd : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      HasDerivAt (f n) (f' n x) x := by
    intro n x hx
    have hnorm : HasDerivAt (wiredNormalizedTheta d q beta0 n) (f' n x) x := by
      by_cases hn0 : n = 0
      · subst n
        have hf0 : wiredNormalizedTheta d q beta0 0 =
            fun _ => 1 / wiredSharpConstant d beta0 := by
          funext z
          simp [wiredNormalizedTheta, wiredOuterInnerTheta]
        rw [hf0]
        simpa [f', wiredNormalizedThetaPrime, wiredOuterInnerThetaPrime,
          wiredOuterInnerTheta] using
          (hasDerivAt_const x (1 / wiredSharpConstant d beta0))
      · exact hasDerivAt_wiredNormalizedTheta d n
          (Nat.one_le_iff_ne_zero.mpr hn0) q beta0 x hq (hinterval x hx)
    refine hnorm.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (hinterval x hx)] with z hz
    have hz0 : 0 < z := hz
    simp [f, wiredThresholdTheta, not_le.mpr hz0]
  have hfnn : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      0 <= f n x := by
    intro n x hx
    rw [show f n x = wiredNormalizedTheta d q beta0 n x by
      simp [f, wiredThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact wiredNormalizedTheta_nonneg d n q beta0 x hq (hinterval x hx)
  have hfM : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      f n x <= M := by
    intro n x hx
    rw [show f n x = wiredNormalizedTheta d q beta0 n x by
      simp [f, wiredThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact wiredNormalizedTheta_le_invConstant d n q beta0 x hq (hinterval x hx)
  have hfmono : ∀ k : Nat, ∀ ⦃y x⦄,
      y ∈ Set.Icc (beta - 2 * delta) beta →
      x ∈ Set.Icc (beta - 2 * delta) beta → y <= x →
      f k y <= f k x := by
    intro k y x hy hx hyx
    rw [show f k y = wiredNormalizedTheta d q beta0 k y by
      simp [f, wiredThresholdTheta, not_le.mpr (hinterval y hy)]]
    rw [show f k x = wiredNormalizedTheta d q beta0 k x by
      simp [f, wiredThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact wiredNormalizedTheta_mono_beta d k q beta0 y x hq
      (hinterval y hy) hyx
  have hSpos : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        0 < IntegrationSubcritical.Sig f n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n x by
      simpa [f] using thresholdSig_of_pos d n q beta0 x (hinterval x hx)]
    exact normalizedSig_pos d n hn q beta0 x hq (hinterval x hx)
  have hdiff : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        ((n : Real) / IntegrationSubcritical.Sig f n x) * f n x <= f' n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n x by
      simpa [f] using thresholdSig_of_pos d n q beta0 x (hinterval x hx)]
    rw [show f n x = wiredNormalizedTheta d q beta0 n x by
      simp [f, wiredThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact wiredNormalizedTheta_differential d n hn q x beta0 hq
      (hinterval x hx) (hx.2.trans hbeta0)
  have hSbeta : ∀ n : Nat, 2 <= n →
      0 < IntegrationSubcritical.Sig f n beta := by
    intro n hn
    rw [show IntegrationSubcritical.Sig f n beta =
        IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta by
      simpa [f] using thresholdSig_of_pos d n q beta0 beta
        (hleft.trans (by linarith [hdelta] : beta - 2 * delta < beta))]
    exact normalizedSig_pos d n (by omega) q beta0 beta hq
      (hleft.trans (by linarith [hdelta] : beta - 2 * delta < beta))
  have hlinear : ∀ n : Nat,
      IntegrationSubcritical.Sig f n beta <= C * (n : Real) := by
    intro n
    unfold IntegrationSubcritical.Sig
    calc
      ∑ k ∈ Finset.range n, f k beta <=
          ∑ _k ∈ Finset.range n, C := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hfM k beta ⟨by linarith [hdelta], le_rfl⟩).trans hMC
      _ = C * (n : Real) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hbdd := BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig f n beta) C hC hSbeta hlinear
  have hbddSet : BddBelow (BetaThresholdBound.thresholdSet
      (fun b n => IntegrationSubcritical.Sig f n b)) := by
    simpa [f] using wiredThresholdSet_bddBelow d q beta0
  obtain ⟨Q, hQ, hdecay⟩ :=
    BetaThresholdBound.btb_subcritical_decay_of_threshold
      f f' delta beta M hdelta hM hd hfnn hfM hfmono hSpos hdiff
      hSbeta hbddSet hbdd hlt
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have hnDecay := hdecay n hn
  have hbeta2 : ¬ beta <= delta * 2 := by linarith [hleft]
  have hdiv : wiredOuterInnerTheta d q (beta - 2 * delta) n / c <=
      Real.exp (-(((n : Real) / Q) * delta)) / c := by
    simpa [f, M, c, wiredThresholdTheta, wiredNormalizedTheta,
      hbeta2, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using hnDecay
  exact (div_le_div_iff_of_pos_right hc).mp hdiv



theorem wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
    (d n : Nat) (hn : 1 <= n) (beta : Real) (hbeta : 0 < beta) :
    wiredOuterInnerTheta d 2 beta n =
      (FK.wiredFiniteMeasure d (2 * n)
          (by
            have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
            linarith : 0 < 1 - Real.exp (-beta))
          (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
          (by norm_num : (0 : Real) < 2) :
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
  have hmass := FK.wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) (2 * n) hp hp1 (centeredShellEvent d n) hmeas
  have htheta := wiredOuterInnerTheta_eq_centeredShellMass
    d n hn 2 beta (by norm_num) hbeta
  rw [hevent] at hmass
  change wiredOuterInnerTheta d 2 beta n =
    (FK.wiredFiniteMeasure d (2 * n) hp hp1
      (by norm_num : (0 : Real) < 2) : Measure _).real
        (FK.boxBdryConnEvent d n)
  rw [htheta]
  exact hmass.symm



theorem wiredOuterInnerTheta_tendsto_fkTheta_q2
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    Filter.Tendsto (fun n => wiredOuterInnerTheta d 2 beta n) Filter.atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (by norm_num : (0 : Real) < 2) (q := 2))) := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let a : Nat → Real := fun n =>
    (FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (FK.boxBdryConnEvent d n)
  let b : Nat → Real := fun n => wiredOuterInnerTheta d 2 beta n
  let thetaInf := FK.fkTheta d hp hp1 (by norm_num : (0 : Real) < 2) (q := 2)
  have ha : Filter.Tendsto a Filter.atTop (nhds thetaInf) := by
    simpa [a, thetaInf] using FK.boxBdryConnEvent_diag_tendsto
      (d := d) hp hp1
  have htwo : Filter.Tendsto (fun n : Nat => 2 * n) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun N => ?_)
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have ha2 : Filter.Tendsto (fun n => a (2 * n)) Filter.atTop (nhds thetaInf) :=
    ha.comp htwo
  have hlower : Filter.Eventually (fun n => a (2 * n) <= b n) Filter.atTop := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (2 * n) hp hp1
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double d n hn beta hbeta]
    exact measureReal_mono
      (FK.boxBdryConnEvent_subset_le n (2 * n) hn (n_le_two_mul n))
      (measure_ne_top _ _)
  have hupper : Filter.Eventually (fun n => b n <= a n) Filter.atTop := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (n + n) hp hp1
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p, two_mul] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double d n hn beta hbeta]
    have hanti := FK.radius_antitone (d := d) n hp hp1 (Nat.zero_le n)
    simpa [a] using hanti
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ha2 ha hlower hupper

theorem wiredThresholdTheta_tendsto_fkTheta_div_q2
    (d : Nat) (beta0 beta : Real) (hbeta : 0 < beta) :
    Filter.Tendsto (fun n => wiredThresholdTheta d 2 beta0 n beta)
      Filter.atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (by norm_num : (0 : Real) < 2) (q := 2) /
          wiredSharpConstant d beta0)) := by
  have hraw := wiredOuterInnerTheta_tendsto_fkTheta_q2 d beta hbeta
  have hdiv := hraw.div_const (wiredSharpConstant d beta0)
  simpa [wiredThresholdTheta, not_le.mpr hbeta, wiredNormalizedTheta] using hdiv

theorem wiredThresholdSet_mem_of_fkTheta_pos_q2
    (d : Nat) (beta0 beta : Real) (hbeta : 0 < beta)
    (hTheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2)) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b) := by
  let L := FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) /
        wiredSharpConstant d beta0
  have hL : 0 < L := div_pos hTheta (wiredSharpConstant_pos d beta0)
  have hconv : Filter.Tendsto
      (fun n => wiredThresholdTheta d 2 beta0 n beta)
      Filter.atTop (nhds L) := by
    simpa [L] using wiredThresholdTheta_tendsto_fkTheta_div_q2
      d beta0 beta hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 <= Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d 2 beta0) n beta)) Filter.atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]

theorem wiredThresholdSet_nonempty_of_fkTheta_pos_q2
    (d : Nat) (beta0 beta : Real) (hbeta : 0 < beta)
    (hTheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2)) :
    (BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n b)).Nonempty :=
  ⟨beta, wiredThresholdSet_mem_of_fkTheta_pos_q2
    d beta0 beta hbeta hTheta⟩

end WiredBoxSharpness
end OSSS
end StatMech
