/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.HexagonalSharpnessOffCentre
import Code.OSSS.BetaThresholdBound
import Code.OSSS.LogCesaroLimit





open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS

noncomputable def hexagonalNormalizedTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  hexagonalOuterInnerTheta q beta n / hexagonalSharpConstant beta0

noncomputable def hexagonalNormalizedThetaPrime
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  hexagonalOuterInnerThetaPrime n q beta / hexagonalSharpConstant beta0

noncomputable def hexagonalThresholdTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / hexagonalSharpConstant beta0 else 0
  else hexagonalNormalizedTheta q beta0 n beta

theorem hexagonalSharpConstant_le_one (beta0 : Real)
    (hbeta0 : 0 <= beta0) : hexagonalSharpConstant beta0 <= 1 := by
  have he0 : 0 <= Real.exp (-beta0) := (Real.exp_pos _).le
  have he1 : Real.exp (-beta0) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hp := pow_le_one₀ he0 he1 (n := 6)
  unfold hexagonalSharpConstant
  nlinarith

theorem one_le_inv_hexagonalSharpConstant (beta0 : Real)
    (hbeta0 : 0 <= beta0) : 1 <= 1 / hexagonalSharpConstant beta0 :=
  one_le_one_div (hexagonalSharpConstant_pos beta0)
    (hexagonalSharpConstant_le_one beta0 hbeta0)

theorem hexagonalOuterInnerTheta_eq_activeBCMean
    (n : Nat) (hn : 1 <= n) (q beta : Real) :
    hexagonalOuterInnerTheta q beta n =
      FK.activeBCMean (hexagonalBoxGraph (2 * n))
        (hexagonalBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q
        (hexagonalInnerCrossInd n) := by
  rw [hexagonalOuterInnerTheta, if_neg (by omega)]
  rfl

theorem hasDerivAt_hexagonalOuterInnerTheta
    (n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (fun b => hexagonalOuterInnerTheta q b n)
      (hexagonalOuterInnerThetaPrime n q beta) beta := by
  have hJ : forall e : Sym2 (HexagonalBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have h := FK.hasDerivAt_activeBCMean_beta_sum
    (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    hJ hbeta (zero_lt_one.trans_le hq) (hexagonalInnerCrossInd n)
  have heq : (fun b => hexagonalOuterInnerTheta q b n) =
      (fun b => FK.activeBCMean (hexagonalBoxGraph (2 * n))
        (hexagonalBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) b) q
        (hexagonalInnerCrossInd n)) := by
    funext b
    exact hexagonalOuterInnerTheta_eq_activeBCMean n hn q b
  rw [heq]
  unfold hexagonalOuterInnerThetaPrime
  rw [heq]
  exact h.congr_deriv h.deriv.symm

theorem hexagonalNormalizedSig_eq
    (n : Nat) (q beta0 beta : Real) :
    IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta =
      hexagonalOuterInnerSig n q beta / hexagonalSharpConstant beta0 := by
  unfold IntegrationSubcritical.Sig hexagonalNormalizedTheta
    hexagonalOuterInnerSig
  rw [Finset.sum_div]

theorem hexagonalNormalizedTheta_differential
    (n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (((n : Real) /
        IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta) *
      hexagonalNormalizedTheta q beta0 n beta) <=
        hexagonalNormalizedThetaPrime q beta0 n beta := by
  have hc := hexagonalSharpConstant_pos beta0
  have hsig := hexagonalOuterInnerSig_pos n hn q beta hq hbeta
  have hmain := hexagonal_outer_inner_differential_uniform
    n hn q beta beta0 hq hbeta hbeta0
  rw [hexagonalNormalizedSig_eq]
  unfold hexagonalNormalizedTheta hexagonalNormalizedThetaPrime
  rw [le_div_iff₀ hc]
  convert hmain using 1 <;> field_simp <;> ring

theorem hasDerivAt_hexagonalNormalizedTheta
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (hexagonalNormalizedTheta q beta0 n)
      (hexagonalNormalizedThetaPrime q beta0 n beta) beta := by
  have h := hasDerivAt_hexagonalOuterInnerTheta n hn q beta hq hbeta
  simpa [hexagonalNormalizedTheta, hexagonalNormalizedThetaPrime] using
    h.div_const (hexagonalSharpConstant beta0)

theorem hexagonalOuterInnerTheta_le_one
    (n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta n <= 1 := by
  by_cases hn0 : n = 0
  · simp [hexagonalOuterInnerTheta, hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (HexagonalBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0
  rw [hexagonalOuterInnerTheta_eq_activeBCMean n hn q beta]
  calc
    FK.activeBCMean (hexagonalBoxGraph (2 * n))
        (hexagonalBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q (hexagonalInnerCrossInd n) <=
      Lindeberg.mean mu (fun _ => (1 : Real)) := by
        unfold FK.activeBCMean Lindeberg.mean mu
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        unfold hexagonalInnerCrossInd
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hmu1 1

theorem hexagonalNormalizedTheta_nonneg
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= hexagonalNormalizedTheta q beta0 n beta := by
  exact div_nonneg
    (hexagonalOuterInnerTheta_nonneg q beta hq hbeta n)
    (hexagonalSharpConstant_pos beta0).le

theorem hexagonalNormalizedTheta_le_invConstant
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    hexagonalNormalizedTheta q beta0 n beta <=
      1 / hexagonalSharpConstant beta0 := by
  unfold hexagonalNormalizedTheta
  exact div_le_div_of_nonneg_right
    (hexagonalOuterInnerTheta_le_one n q beta hq hbeta)
    (hexagonalSharpConstant_pos beta0).le

theorem hexagonalNormalizedSig_pos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < IntegrationSubcritical.Sig
      (hexagonalNormalizedTheta q beta0) n beta := by
  rw [hexagonalNormalizedSig_eq]
  exact div_pos (hexagonalOuterInnerSig_pos n hn q beta hq hbeta)
    (hexagonalSharpConstant_pos beta0)

theorem hexagonalOuterInnerThetaPrime_nonneg
    (n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= hexagonalOuterInnerThetaPrime n q beta := by
  have hlog := hexagonal_outer_inner_differential_sharp
    n hn q beta hq hbeta
  have htheta0 := hexagonalOuterInnerTheta_nonneg q beta hq hbeta n
  have htheta1 := hexagonalOuterInnerTheta_le_one n q beta hq hbeta
  have hsig := hexagonalOuterInnerSig_pos n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < 8 * hexagonalOuterInnerSig n q beta / (n : Real) := by
    positivity
  have hnonneg : 0 <= hexagonalOuterInnerTheta q beta n *
      (1 - hexagonalOuterInnerTheta q beta n) /
        (8 * hexagonalOuterInnerSig n q beta / (n : Real)) :=
    div_nonneg (mul_nonneg htheta0 (sub_nonneg.mpr htheta1)) hden.le
  exact hnonneg.trans hlog

theorem hexagonalNormalizedThetaPrime_nonneg
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= hexagonalNormalizedThetaPrime q beta0 n beta := by
  unfold hexagonalNormalizedThetaPrime
  exact div_nonneg
    (hexagonalOuterInnerThetaPrime_nonneg n hn q beta hq hbeta)
    (hexagonalSharpConstant_pos beta0).le

theorem hexagonalNormalizedTheta_mono_beta
    (n : Nat) (q beta0 y x : Real) (hq : 1 <= q)
    (hy : 0 < y) (hyx : y <= x) :
    hexagonalNormalizedTheta q beta0 n y <=
      hexagonalNormalizedTheta q beta0 n x := by
  by_cases hn0 : n = 0
  · subst n
    simp [hexagonalNormalizedTheta, hexagonalOuterInnerTheta]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let f := hexagonalNormalizedTheta q beta0 n
  let f' := hexagonalNormalizedThetaPrime q beta0 n
  have hd : ∀ z, z ∈ Set.Icc y x → HasDerivAt f (f' z) z := by
    intro z hz
    exact hasDerivAt_hexagonalNormalizedTheta n hn q beta0 z hq
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
      exact hexagonalNormalizedThetaPrime_nonneg n hn q beta0 z hq
        (hy.trans hz.1)
  exact hmono (Set.left_mem_Icc.mpr hyx) (Set.right_mem_Icc.mpr hyx) hyx

theorem hexagonalThresholdTheta_of_pos
    (n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    hexagonalThresholdTheta q beta0 n beta =
      hexagonalNormalizedTheta q beta0 n beta := by
  simp [hexagonalThresholdTheta, not_le.mpr hbeta]

theorem hexagonalThresholdSig_of_pos
    (n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta =
      IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta := by
  unfold IntegrationSubcritical.Sig
  apply Finset.sum_congr rfl
  intro k hk
  exact hexagonalThresholdTheta_of_pos k q beta0 beta hbeta

theorem hexagonalThresholdSig_of_nonpos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hbeta : beta <= 0) :
    IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta =
      1 / hexagonalSharpConstant beta0 := by
  unfold IntegrationSubcritical.Sig hexagonalThresholdTheta
  simp only [if_pos hbeta]
  rw [Finset.sum_eq_single 0]
  · simp [(hexagonalSharpConstant_pos beta0).ne']
  · intro k hk hk0
    simp [hk0]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hn)).elim

theorem hexagonalThresholdSet_bddBelow (q beta0 : Real) :
    BddBelow (BetaThresholdBound.thresholdSet
      (fun b n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n b)) := by
  refine ⟨0, ?_⟩
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Filter.Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig
          (hexagonalThresholdTheta q beta0) n beta))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun n : Nat => Real.log (n : Real))
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Filter.Tendsto (fun n : Nat =>
        Real.log (1 / hexagonalSharpConstant beta0) /
          Real.log (n : Real)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / hexagonalSharpConstant beta0) /
        Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [hexagonalThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  have hlimsup := htend.limsup_eq
  change 1 <= Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)) Filter.atTop at hmem
  rw [hlimsup] at hmem
  linarith

theorem hexagonalThresholdTheta_nonneg
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    0 <= hexagonalThresholdTheta q beta0 n beta := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [hexagonalThresholdTheta, if_pos hbeta, if_pos hn0]
      exact (div_pos one_pos (hexagonalSharpConstant_pos beta0)).le
    · rw [hexagonalThresholdTheta, if_pos hbeta, if_neg hn0]
  · rw [hexagonalThresholdTheta_of_pos n q beta0 beta (lt_of_not_ge hbeta)]
    exact hexagonalNormalizedTheta_nonneg n q beta0 beta hq
      (lt_of_not_ge hbeta)

theorem hexagonalThresholdTheta_le_invConstant
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    hexagonalThresholdTheta q beta0 n beta <=
      1 / hexagonalSharpConstant beta0 := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [hexagonalThresholdTheta, if_pos hbeta, if_pos hn0]
    · rw [hexagonalThresholdTheta, if_pos hbeta, if_neg hn0]
      exact (div_pos one_pos (hexagonalSharpConstant_pos beta0)).le
  · rw [hexagonalThresholdTheta_of_pos n q beta0 beta (lt_of_not_ge hbeta)]
    exact hexagonalNormalizedTheta_le_invConstant n q beta0 beta hq
      (lt_of_not_ge hbeta)

theorem hexagonalThresholdTheta_mono_beta
    (n : Nat) (q beta0 a b : Real) (hq : 1 <= q) (hab : a <= b) :
    hexagonalThresholdTheta q beta0 n a <=
      hexagonalThresholdTheta q beta0 n b := by
  by_cases hb : b <= 0
  · have ha : a <= 0 := hab.trans hb
    simp [hexagonalThresholdTheta, ha, hb]
  by_cases ha : a <= 0
  · by_cases hn0 : n = 0
    · subst n
      simp [hexagonalThresholdTheta, ha, hb, hexagonalNormalizedTheta,
        hexagonalOuterInnerTheta]
    · rw [hexagonalThresholdTheta, if_pos ha, if_neg hn0,
        hexagonalThresholdTheta, if_neg hb]
      exact hexagonalNormalizedTheta_nonneg n q beta0 b hq (lt_of_not_ge hb)
  · rw [hexagonalThresholdTheta_of_pos n q beta0 a (lt_of_not_ge ha),
      hexagonalThresholdTheta_of_pos n q beta0 b (lt_of_not_ge hb)]
    exact hexagonalNormalizedTheta_mono_beta n q beta0 a b hq
      (lt_of_not_ge ha) hab

theorem hexagonalThresholdSig_mono_beta
    (n : Nat) (q beta0 : Real) (hq : 1 <= q)
    {a b : Real} (hab : a <= b) :
    IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n a <=
      IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b := by
  unfold IntegrationSubcritical.Sig
  exact Finset.sum_le_sum (fun k _ =>
    hexagonalThresholdTheta_mono_beta k q beta0 a b hq hab)

theorem hexagonalThresholdSig_pos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hq : 1 <= q) :
    0 < IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta := by
  have hzero : hexagonalThresholdTheta q beta0 0 beta =
      1 / hexagonalSharpConstant beta0 := by
    by_cases hbeta : beta <= 0
    · simp [hexagonalThresholdTheta, hbeta]
    · simp [hexagonalThresholdTheta, hbeta, hexagonalNormalizedTheta,
        hexagonalOuterInnerTheta]
  have hsum : hexagonalThresholdTheta q beta0 0 beta <=
      IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta := by
    unfold IntegrationSubcritical.Sig
    apply Finset.single_le_sum
      (fun k _ => hexagonalThresholdTheta_nonneg k q beta0 beta hq)
    simpa using hn
  rw [hzero] at hsum
  exact (div_pos zero_lt_one (hexagonalSharpConstant_pos beta0)).trans_le hsum

theorem hexagonalThresholdSig_le_linear
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta <=
      (1 / hexagonalSharpConstant beta0) * (n : Real) := by
  unfold IntegrationSubcritical.Sig
  calc
    ∑ k ∈ Finset.range n, hexagonalThresholdTheta q beta0 k beta <=
        ∑ _k ∈ Finset.range n, (1 / hexagonalSharpConstant beta0) := by
      exact Finset.sum_le_sum (fun k _ =>
        hexagonalThresholdTheta_le_invConstant k q beta0 beta hq)
    _ = (1 / hexagonalSharpConstant beta0) * (n : Real) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring



theorem hexagonalOuterInner_subcritical_decay_of_threshold
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0)
    (hdelta : 0 < delta) (hleft : 0 < beta - 2 * delta)
    (hlt : beta < BetaThresholdBound.beta1
      (fun b n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n b)) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      hexagonalOuterInnerTheta q (beta - 2 * delta) n <=
        Real.exp (-(((n : Real) / Q) * delta)) := by
  let f := hexagonalThresholdTheta q beta0
  let f' := hexagonalNormalizedThetaPrime q beta0
  let c := hexagonalSharpConstant beta0
  let M := 1 / c
  let C := max 1 M
  have hc : 0 < c := hexagonalSharpConstant_pos beta0
  have hM : 0 <= M := by unfold M; positivity
  have hC : 1 <= C := le_max_left _ _
  have hMC : M <= C := le_max_right _ _
  have hinterval : ∀ x ∈ Set.Icc (beta - 2 * delta) beta, 0 < x := by
    intro x hx
    exact hleft.trans_le hx.1
  have hd : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      HasDerivAt (f n) (f' n x) x := by
    intro n x hx
    have hnorm : HasDerivAt (hexagonalNormalizedTheta q beta0 n)
        (f' n x) x := by
      by_cases hn0 : n = 0
      · subst n
        have hf0 : hexagonalNormalizedTheta q beta0 0 =
            fun _ => 1 / hexagonalSharpConstant beta0 := by
          funext z
          simp [hexagonalNormalizedTheta, hexagonalOuterInnerTheta]
        rw [hf0]
        simpa [f', hexagonalNormalizedThetaPrime,
          hexagonalOuterInnerThetaPrime, hexagonalOuterInnerTheta] using
          (hasDerivAt_const x (1 / hexagonalSharpConstant beta0))
      · exact hasDerivAt_hexagonalNormalizedTheta n
          (Nat.one_le_iff_ne_zero.mpr hn0) q beta0 x hq (hinterval x hx)
    refine hnorm.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (hinterval x hx)] with z hz
    have hz0 : 0 < z := hz
    simp [f, hexagonalThresholdTheta, not_le.mpr hz0]
  have hfnn : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      0 <= f n x := by
    intro n x hx
    rw [show f n x = hexagonalNormalizedTheta q beta0 n x by
      simp [f, hexagonalThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact hexagonalNormalizedTheta_nonneg n q beta0 x hq (hinterval x hx)
  have hfM : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      f n x <= M := by
    intro n x hx
    rw [show f n x = hexagonalNormalizedTheta q beta0 n x by
      simp [f, hexagonalThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact hexagonalNormalizedTheta_le_invConstant n q beta0 x hq
      (hinterval x hx)
  have hfmono : ∀ k : Nat, ∀ ⦃y x⦄,
      y ∈ Set.Icc (beta - 2 * delta) beta →
      x ∈ Set.Icc (beta - 2 * delta) beta → y <= x →
      f k y <= f k x := by
    intro k y x hy hx hyx
    rw [show f k y = hexagonalNormalizedTheta q beta0 k y by
      simp [f, hexagonalThresholdTheta, not_le.mpr (hinterval y hy)]]
    rw [show f k x = hexagonalNormalizedTheta q beta0 k x by
      simp [f, hexagonalThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact hexagonalNormalizedTheta_mono_beta k q beta0 y x hq
      (hinterval y hy) hyx
  have hSpos : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        0 < IntegrationSubcritical.Sig f n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n x by
      simpa [f] using hexagonalThresholdSig_of_pos n q beta0 x
        (hinterval x hx)]
    exact hexagonalNormalizedSig_pos n hn q beta0 x hq (hinterval x hx)
  have hdiff : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        ((n : Real) / IntegrationSubcritical.Sig f n x) * f n x <=
          f' n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n x by
      simpa [f] using hexagonalThresholdSig_of_pos n q beta0 x
        (hinterval x hx)]
    rw [show f n x = hexagonalNormalizedTheta q beta0 n x by
      simp [f, hexagonalThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact hexagonalNormalizedTheta_differential n hn q x beta0 hq
      (hinterval x hx) (hx.2.trans hbeta0)
  have hbetapos : 0 < beta := hleft.trans (by linarith [hdelta])
  have hSbeta : ∀ n : Nat, 2 <= n →
      0 < IntegrationSubcritical.Sig f n beta := by
    intro n hn
    rw [show IntegrationSubcritical.Sig f n beta =
        IntegrationSubcritical.Sig
          (hexagonalNormalizedTheta q beta0) n beta by
      simpa [f] using hexagonalThresholdSig_of_pos n q beta0 beta hbetapos]
    exact hexagonalNormalizedSig_pos n (by omega) q beta0 beta hq hbetapos
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
    simpa [f] using hexagonalThresholdSet_bddBelow q beta0
  obtain ⟨Q, hQ, hdecay⟩ :=
    BetaThresholdBound.btb_subcritical_decay_of_threshold
      f f' delta beta M hdelta hM hd hfnn hfM hfmono hSpos hdiff
      hSbeta hbddSet hbdd hlt
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have hnDecay := hdecay n hn
  have hbeta2 : ¬ beta <= delta * 2 := by linarith [hleft]
  have hdiv : hexagonalOuterInnerTheta q (beta - 2 * delta) n / c <=
      Real.exp (-(((n : Real) / Q) * delta)) / c := by
    simpa [f, M, c, hexagonalThresholdTheta, hexagonalNormalizedTheta,
      hbeta2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnDecay
  exact (div_le_div_iff_of_pos_right hc).mp hdiv

end StatMech.FK.PeriodicPlanar
