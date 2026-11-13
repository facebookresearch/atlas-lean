/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriangularSharpnessOffCentre
import Code.OSSS.BetaThresholdBound
import Code.OSSS.LogCesaroLimit





open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS

noncomputable def triangularNormalizedTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  triangularOuterInnerTheta q beta n / triangularSharpConstant beta0

noncomputable def triangularNormalizedThetaPrime
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  triangularOuterInnerThetaPrime n q beta / triangularSharpConstant beta0

noncomputable def triangularThresholdTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / triangularSharpConstant beta0 else 0
  else triangularNormalizedTheta q beta0 n beta

theorem triangularSharpConstant_le_one (beta0 : Real)
    (hbeta0 : 0 <= beta0) : triangularSharpConstant beta0 <= 1 := by
  have he0 : 0 <= Real.exp (-beta0) := (Real.exp_pos _).le
  have he1 : Real.exp (-beta0) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hp := pow_le_one₀ he0 he1 (n := 6)
  unfold triangularSharpConstant
  nlinarith

theorem one_le_inv_triangularSharpConstant (beta0 : Real)
    (hbeta0 : 0 <= beta0) : 1 <= 1 / triangularSharpConstant beta0 :=
  one_le_one_div (triangularSharpConstant_pos beta0)
    (triangularSharpConstant_le_one beta0 hbeta0)

theorem triangularOuterInnerTheta_eq_activeBCMean
    (n : Nat) (hn : 1 <= n) (q beta : Real) :
    triangularOuterInnerTheta q beta n =
      FK.activeBCMean (triangularBoxGraph (2 * n))
        (triangularBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q
        (triangularInnerCrossInd n) := by
  rw [triangularOuterInnerTheta, if_neg (by omega)]
  rfl

theorem hasDerivAt_triangularOuterInnerTheta
    (n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (fun b => triangularOuterInnerTheta q b n)
      (triangularOuterInnerThetaPrime n q beta) beta := by
  have hJ : forall e : Sym2 (TriangularBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have h := FK.hasDerivAt_activeBCMean_beta_sum
    (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    hJ hbeta (zero_lt_one.trans_le hq) (triangularInnerCrossInd n)
  have heq : (fun b => triangularOuterInnerTheta q b n) =
      (fun b => FK.activeBCMean (triangularBoxGraph (2 * n))
        (triangularBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) b) q
        (triangularInnerCrossInd n)) := by
    funext b
    exact triangularOuterInnerTheta_eq_activeBCMean n hn q b
  rw [heq]
  unfold triangularOuterInnerThetaPrime
  rw [heq]
  exact h.congr_deriv h.deriv.symm

theorem triangularNormalizedSig_eq
    (n : Nat) (q beta0 beta : Real) :
    IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta =
      triangularOuterInnerSig n q beta / triangularSharpConstant beta0 := by
  unfold IntegrationSubcritical.Sig triangularNormalizedTheta
    triangularOuterInnerSig
  rw [Finset.sum_div]

theorem triangularNormalizedTheta_differential
    (n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (((n : Real) /
        IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta) *
      triangularNormalizedTheta q beta0 n beta) <=
        triangularNormalizedThetaPrime q beta0 n beta := by
  have hc := triangularSharpConstant_pos beta0
  have hsig := triangularOuterInnerSig_pos n hn q beta hq hbeta
  have hmain := triangular_outer_inner_differential_uniform
    n hn q beta beta0 hq hbeta hbeta0
  rw [triangularNormalizedSig_eq]
  unfold triangularNormalizedTheta triangularNormalizedThetaPrime
  rw [le_div_iff₀ hc]
  convert hmain using 1 <;> field_simp <;> ring

theorem hasDerivAt_triangularNormalizedTheta
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt (triangularNormalizedTheta q beta0 n)
      (triangularNormalizedThetaPrime q beta0 n beta) beta := by
  have h := hasDerivAt_triangularOuterInnerTheta n hn q beta hq hbeta
  simpa [triangularNormalizedTheta, triangularNormalizedThetaPrime] using
    h.div_const (triangularSharpConstant beta0)

theorem triangularOuterInnerTheta_le_one
    (n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta n <= 1 := by
  by_cases hn0 : n = 0
  · simp [triangularOuterInnerTheta, hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (TriangularBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0
  rw [triangularOuterInnerTheta_eq_activeBCMean n hn q beta]
  calc
    FK.activeBCMean (triangularBoxGraph (2 * n))
        (triangularBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q (triangularInnerCrossInd n) <=
      Lindeberg.mean mu (fun _ => (1 : Real)) := by
        unfold FK.activeBCMean Lindeberg.mean mu
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        unfold triangularInnerCrossInd
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hmu1 1

theorem triangularNormalizedTheta_nonneg
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= triangularNormalizedTheta q beta0 n beta := by
  exact div_nonneg
    (triangularOuterInnerTheta_nonneg q beta hq hbeta n)
    (triangularSharpConstant_pos beta0).le

theorem triangularNormalizedTheta_le_invConstant
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    triangularNormalizedTheta q beta0 n beta <=
      1 / triangularSharpConstant beta0 := by
  unfold triangularNormalizedTheta
  exact div_le_div_of_nonneg_right
    (triangularOuterInnerTheta_le_one n q beta hq hbeta)
    (triangularSharpConstant_pos beta0).le

theorem triangularNormalizedSig_pos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < IntegrationSubcritical.Sig
      (triangularNormalizedTheta q beta0) n beta := by
  rw [triangularNormalizedSig_eq]
  exact div_pos (triangularOuterInnerSig_pos n hn q beta hq hbeta)
    (triangularSharpConstant_pos beta0)

theorem triangularOuterInnerThetaPrime_nonneg
    (n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= triangularOuterInnerThetaPrime n q beta := by
  have hlog := triangular_outer_inner_differential_sharp
    n hn q beta hq hbeta
  have htheta0 := triangularOuterInnerTheta_nonneg q beta hq hbeta n
  have htheta1 := triangularOuterInnerTheta_le_one n q beta hq hbeta
  have hsig := triangularOuterInnerSig_pos n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < 8 * triangularOuterInnerSig n q beta / (n : Real) := by
    positivity
  have hnonneg : 0 <= triangularOuterInnerTheta q beta n *
      (1 - triangularOuterInnerTheta q beta n) /
        (8 * triangularOuterInnerSig n q beta / (n : Real)) :=
    div_nonneg (mul_nonneg htheta0 (sub_nonneg.mpr htheta1)) hden.le
  exact hnonneg.trans hlog

theorem triangularNormalizedThetaPrime_nonneg
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= triangularNormalizedThetaPrime q beta0 n beta := by
  unfold triangularNormalizedThetaPrime
  exact div_nonneg
    (triangularOuterInnerThetaPrime_nonneg n hn q beta hq hbeta)
    (triangularSharpConstant_pos beta0).le

theorem triangularNormalizedTheta_mono_beta
    (n : Nat) (q beta0 y x : Real) (hq : 1 <= q)
    (hy : 0 < y) (hyx : y <= x) :
    triangularNormalizedTheta q beta0 n y <=
      triangularNormalizedTheta q beta0 n x := by
  by_cases hn0 : n = 0
  · subst n
    simp [triangularNormalizedTheta, triangularOuterInnerTheta]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let f := triangularNormalizedTheta q beta0 n
  let f' := triangularNormalizedThetaPrime q beta0 n
  have hd : ∀ z, z ∈ Set.Icc y x → HasDerivAt f (f' z) z := by
    intro z hz
    exact hasDerivAt_triangularNormalizedTheta n hn q beta0 z hq
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
      exact triangularNormalizedThetaPrime_nonneg n hn q beta0 z hq
        (hy.trans hz.1)
  exact hmono (Set.left_mem_Icc.mpr hyx) (Set.right_mem_Icc.mpr hyx) hyx

theorem triangularThresholdTheta_of_pos
    (n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    triangularThresholdTheta q beta0 n beta =
      triangularNormalizedTheta q beta0 n beta := by
  simp [triangularThresholdTheta, not_le.mpr hbeta]

theorem triangularThresholdSig_of_pos
    (n : Nat) (q beta0 beta : Real) (hbeta : 0 < beta) :
    IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta =
      IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta := by
  unfold IntegrationSubcritical.Sig
  apply Finset.sum_congr rfl
  intro k hk
  exact triangularThresholdTheta_of_pos k q beta0 beta hbeta

theorem triangularThresholdSig_of_nonpos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hbeta : beta <= 0) :
    IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta =
      1 / triangularSharpConstant beta0 := by
  unfold IntegrationSubcritical.Sig triangularThresholdTheta
  simp only [if_pos hbeta]
  rw [Finset.sum_eq_single 0]
  · simp [(triangularSharpConstant_pos beta0).ne']
  · intro k hk hk0
    simp [hk0]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hn)).elim

theorem triangularThresholdSet_bddBelow (q beta0 : Real) :
    BddBelow (BetaThresholdBound.thresholdSet
      (fun b n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n b)) := by
  refine ⟨0, ?_⟩
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Filter.Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig
          (triangularThresholdTheta q beta0) n beta))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun n : Nat => Real.log (n : Real))
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Filter.Tendsto (fun n : Nat =>
        Real.log (1 / triangularSharpConstant beta0) /
          Real.log (n : Real)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / triangularSharpConstant beta0) /
        Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [triangularThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  have hlimsup := htend.limsup_eq
  change 1 <= Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)) Filter.atTop at hmem
  rw [hlimsup] at hmem
  linarith

theorem triangularThresholdTheta_nonneg
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    0 <= triangularThresholdTheta q beta0 n beta := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [triangularThresholdTheta, if_pos hbeta, if_pos hn0]
      exact (div_pos one_pos (triangularSharpConstant_pos beta0)).le
    · rw [triangularThresholdTheta, if_pos hbeta, if_neg hn0]
  · rw [triangularThresholdTheta_of_pos n q beta0 beta (lt_of_not_ge hbeta)]
    exact triangularNormalizedTheta_nonneg n q beta0 beta hq
      (lt_of_not_ge hbeta)

theorem triangularThresholdTheta_le_invConstant
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    triangularThresholdTheta q beta0 n beta <=
      1 / triangularSharpConstant beta0 := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [triangularThresholdTheta, if_pos hbeta, if_pos hn0]
    · rw [triangularThresholdTheta, if_pos hbeta, if_neg hn0]
      exact (div_pos one_pos (triangularSharpConstant_pos beta0)).le
  · rw [triangularThresholdTheta_of_pos n q beta0 beta (lt_of_not_ge hbeta)]
    exact triangularNormalizedTheta_le_invConstant n q beta0 beta hq
      (lt_of_not_ge hbeta)

theorem triangularThresholdTheta_mono_beta
    (n : Nat) (q beta0 a b : Real) (hq : 1 <= q) (hab : a <= b) :
    triangularThresholdTheta q beta0 n a <=
      triangularThresholdTheta q beta0 n b := by
  by_cases hb : b <= 0
  · have ha : a <= 0 := hab.trans hb
    simp [triangularThresholdTheta, ha, hb]
  by_cases ha : a <= 0
  · by_cases hn0 : n = 0
    · subst n
      simp [triangularThresholdTheta, ha, hb, triangularNormalizedTheta,
        triangularOuterInnerTheta]
    · rw [triangularThresholdTheta, if_pos ha, if_neg hn0,
        triangularThresholdTheta, if_neg hb]
      exact triangularNormalizedTheta_nonneg n q beta0 b hq (lt_of_not_ge hb)
  · rw [triangularThresholdTheta_of_pos n q beta0 a (lt_of_not_ge ha),
      triangularThresholdTheta_of_pos n q beta0 b (lt_of_not_ge hb)]
    exact triangularNormalizedTheta_mono_beta n q beta0 a b hq
      (lt_of_not_ge ha) hab

theorem triangularThresholdSig_mono_beta
    (n : Nat) (q beta0 : Real) (hq : 1 <= q)
    {a b : Real} (hab : a <= b) :
    IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n a <=
      IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b := by
  unfold IntegrationSubcritical.Sig
  exact Finset.sum_le_sum (fun k _ =>
    triangularThresholdTheta_mono_beta k q beta0 a b hq hab)

theorem triangularThresholdSig_pos
    (n : Nat) (hn : 1 <= n) (q beta0 beta : Real) (hq : 1 <= q) :
    0 < IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta := by
  have hzero : triangularThresholdTheta q beta0 0 beta =
      1 / triangularSharpConstant beta0 := by
    by_cases hbeta : beta <= 0
    · simp [triangularThresholdTheta, hbeta]
    · simp [triangularThresholdTheta, hbeta, triangularNormalizedTheta,
        triangularOuterInnerTheta]
  have hsum : triangularThresholdTheta q beta0 0 beta <=
      IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta := by
    unfold IntegrationSubcritical.Sig
    apply Finset.single_le_sum
      (fun k _ => triangularThresholdTheta_nonneg k q beta0 beta hq)
    simpa using hn
  rw [hzero] at hsum
  exact (div_pos zero_lt_one (triangularSharpConstant_pos beta0)).trans_le hsum

theorem triangularThresholdSig_le_linear
    (n : Nat) (q beta0 beta : Real) (hq : 1 <= q) :
    IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta <=
      (1 / triangularSharpConstant beta0) * (n : Real) := by
  unfold IntegrationSubcritical.Sig
  calc
    ∑ k ∈ Finset.range n, triangularThresholdTheta q beta0 k beta <=
        ∑ _k ∈ Finset.range n, (1 / triangularSharpConstant beta0) := by
      exact Finset.sum_le_sum (fun k _ =>
        triangularThresholdTheta_le_invConstant k q beta0 beta hq)
    _ = (1 / triangularSharpConstant beta0) * (n : Real) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring



theorem triangularOuterInner_subcritical_decay_of_threshold
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0)
    (hdelta : 0 < delta) (hleft : 0 < beta - 2 * delta)
    (hlt : beta < BetaThresholdBound.beta1
      (fun b n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n b)) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      triangularOuterInnerTheta q (beta - 2 * delta) n <=
        Real.exp (-(((n : Real) / Q) * delta)) := by
  let f := triangularThresholdTheta q beta0
  let f' := triangularNormalizedThetaPrime q beta0
  let c := triangularSharpConstant beta0
  let M := 1 / c
  let C := max 1 M
  have hc : 0 < c := triangularSharpConstant_pos beta0
  have hM : 0 <= M := by unfold M; positivity
  have hC : 1 <= C := le_max_left _ _
  have hMC : M <= C := le_max_right _ _
  have hinterval : ∀ x ∈ Set.Icc (beta - 2 * delta) beta, 0 < x := by
    intro x hx
    exact hleft.trans_le hx.1
  have hd : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      HasDerivAt (f n) (f' n x) x := by
    intro n x hx
    have hnorm : HasDerivAt (triangularNormalizedTheta q beta0 n)
        (f' n x) x := by
      by_cases hn0 : n = 0
      · subst n
        have hf0 : triangularNormalizedTheta q beta0 0 =
            fun _ => 1 / triangularSharpConstant beta0 := by
          funext z
          simp [triangularNormalizedTheta, triangularOuterInnerTheta]
        rw [hf0]
        simpa [f', triangularNormalizedThetaPrime,
          triangularOuterInnerThetaPrime, triangularOuterInnerTheta] using
          (hasDerivAt_const x (1 / triangularSharpConstant beta0))
      · exact hasDerivAt_triangularNormalizedTheta n
          (Nat.one_le_iff_ne_zero.mpr hn0) q beta0 x hq (hinterval x hx)
    refine hnorm.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (hinterval x hx)] with z hz
    have hz0 : 0 < z := hz
    simp [f, triangularThresholdTheta, not_le.mpr hz0]
  have hfnn : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      0 <= f n x := by
    intro n x hx
    rw [show f n x = triangularNormalizedTheta q beta0 n x by
      simp [f, triangularThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact triangularNormalizedTheta_nonneg n q beta0 x hq (hinterval x hx)
  have hfM : ∀ n : Nat, ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
      f n x <= M := by
    intro n x hx
    rw [show f n x = triangularNormalizedTheta q beta0 n x by
      simp [f, triangularThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact triangularNormalizedTheta_le_invConstant n q beta0 x hq
      (hinterval x hx)
  have hfmono : ∀ k : Nat, ∀ ⦃y x⦄,
      y ∈ Set.Icc (beta - 2 * delta) beta →
      x ∈ Set.Icc (beta - 2 * delta) beta → y <= x →
      f k y <= f k x := by
    intro k y x hy hx hyx
    rw [show f k y = triangularNormalizedTheta q beta0 k y by
      simp [f, triangularThresholdTheta, not_le.mpr (hinterval y hy)]]
    rw [show f k x = triangularNormalizedTheta q beta0 k x by
      simp [f, triangularThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact triangularNormalizedTheta_mono_beta k q beta0 y x hq
      (hinterval y hy) hyx
  have hSpos : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        0 < IntegrationSubcritical.Sig f n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n x by
      simpa [f] using triangularThresholdSig_of_pos n q beta0 x
        (hinterval x hx)]
    exact triangularNormalizedSig_pos n hn q beta0 x hq (hinterval x hx)
  have hdiff : ∀ n : Nat, 1 <= n →
      ∀ x ∈ Set.Icc (beta - 2 * delta) beta,
        ((n : Real) / IntegrationSubcritical.Sig f n x) * f n x <=
          f' n x := by
    intro n hn x hx
    rw [show IntegrationSubcritical.Sig f n x =
        IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n x by
      simpa [f] using triangularThresholdSig_of_pos n q beta0 x
        (hinterval x hx)]
    rw [show f n x = triangularNormalizedTheta q beta0 n x by
      simp [f, triangularThresholdTheta, not_le.mpr (hinterval x hx)]]
    exact triangularNormalizedTheta_differential n hn q x beta0 hq
      (hinterval x hx) (hx.2.trans hbeta0)
  have hbetapos : 0 < beta := hleft.trans (by linarith [hdelta])
  have hSbeta : ∀ n : Nat, 2 <= n →
      0 < IntegrationSubcritical.Sig f n beta := by
    intro n hn
    rw [show IntegrationSubcritical.Sig f n beta =
        IntegrationSubcritical.Sig
          (triangularNormalizedTheta q beta0) n beta by
      simpa [f] using triangularThresholdSig_of_pos n q beta0 beta hbetapos]
    exact triangularNormalizedSig_pos n (by omega) q beta0 beta hq hbetapos
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
    simpa [f] using triangularThresholdSet_bddBelow q beta0
  obtain ⟨Q, hQ, hdecay⟩ :=
    BetaThresholdBound.btb_subcritical_decay_of_threshold
      f f' delta beta M hdelta hM hd hfnn hfM hfmono hSpos hdiff
      hSbeta hbddSet hbdd hlt
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have hnDecay := hdecay n hn
  have hbeta2 : ¬ beta <= delta * 2 := by linarith [hleft]
  have hdiv : triangularOuterInnerTheta q (beta - 2 * delta) n / c <=
      Real.exp (-(((n : Real) / Q) * delta)) / c := by
    simpa [f, M, c, triangularThresholdTheta, triangularNormalizedTheta,
      hbeta2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnDecay
  exact (div_le_div_iff_of_pos_right hc).mp hdiv

end StatMech.FK.PeriodicPlanar
