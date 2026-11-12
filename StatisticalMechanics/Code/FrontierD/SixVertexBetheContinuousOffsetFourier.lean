/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierPhysicalDensity
import Code.FrontierD.SixVertexBetheFourierOrthogonality
import Code.FrontierD.SixVertexAntiferroelectricSeries










namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexOffsetCorrectionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  sixVertexGapCorrectionTerm lam n / Real.pi *
    Real.sin ((n + 1 : Real) * alpha)

theorem norm_sixVertexOffsetCorrectionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetCorrectionTerm lam n alpha‖ <=
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by
  rw [sixVertexOffsetCorrectionTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos Real.pi_pos]
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |sixVertexGapCorrectionTerm lam n| / Real.pi *
        |Real.sin ((n + 1 : Real) * alpha)| <=
      ‖sixVertexGapCorrectionTerm lam n‖ / Real.pi * 1 := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hsin (by positivity)
    _ <= (2 * Real.exp (-2 * lam) ^ (n + 1)) / Real.pi := by
      simpa only [mul_one] using div_le_div_of_nonneg_right
        (sixVertexGapCorrectionTerm_norm_le lam n) Real.pi_pos.le
    _ = (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by ring

theorem summable_sixVertexOffsetCorrectionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetCorrectionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetCorrectionTerm_le lam n alpha)

def sixVertexOffsetRapidityProfile (lam alpha : Real) : Real :=
  -alpha / (2 * Real.pi) +
    ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha

theorem continuous_sixVertexOffsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexOffsetRapidityProfile lam) := by
  unfold sixVertexOffsetRapidityProfile
  apply Continuous.add (by fun_prop)
  apply continuous_tsum
  · intro n
    unfold sixVertexOffsetCorrectionTerm
    fun_prop
  · have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
    have hq1 : Real.exp (-2 * lam) < 1 := by
      rw [<- Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  · intro n alpha
    exact norm_sixVertexOffsetCorrectionTerm_le lam n alpha

theorem odd_sixVertexOffsetCorrectionTerm (lam : Real) (n : Nat) :
    Function.Odd (sixVertexOffsetCorrectionTerm lam n) := by
  intro alpha
  unfold sixVertexOffsetCorrectionTerm
  rw [mul_neg, Real.sin_neg]
  ring

theorem odd_sixVertexOffsetRapidityProfile (lam : Real) :
    Function.Odd (sixVertexOffsetRapidityProfile lam) := by
  intro alpha
  unfold sixVertexOffsetRapidityProfile
  have hsum :
      (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n (-alpha)) =
        -(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) := by
    rw [<- tsum_neg]
    apply tsum_congr
    intro n
    exact odd_sixVertexOffsetCorrectionTerm lam n alpha
  rw [hsum]
  ring


def sixVertexContinuousOffsetFourier
    (c : Real) (hc : 2 < c) (x : Real) : Real :=
  sixVertexOffsetRapidityProfile (sixVertexAntiferroelectricLambda c)
    (sixVertexMomentumRapidity (sixVertexAntiferroelectricLambda c)
      (sixVertexAntiferroelectricLambda_pos hc) x)

theorem continuous_sixVertexContinuousOffsetFourier
    {c : Real} (hc : 2 < c) :
    Continuous (sixVertexContinuousOffsetFourier c hc) := by
  exact (continuous_sixVertexOffsetRapidityProfile
      (sixVertexAntiferroelectricLambda_pos hc)).comp
    (continuous_sixVertexMomentumRapidity
      (sixVertexAntiferroelectricLambda_pos hc))

theorem sixVertexContinuousOffsetFourier_rapidityMomentum
    {c : Real} (hc : 2 < c) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexContinuousOffsetFourier c hc
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexOffsetRapidityProfile
        (sixVertexAntiferroelectricLambda c) alpha := by
  unfold sixVertexContinuousOffsetFourier
  rw [sixVertexMomentumRapidity_rapidityMomentum
    (sixVertexAntiferroelectricLambda_pos hc) halpha]

theorem sixVertexRapidityMomentum_neg
    (lam alpha : Real) :
    sixVertexRapidityMomentum lam (-alpha) =
      -sixVertexRapidityMomentum lam alpha := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := sixVertexXiFourier lam) (a := 0) (b := alpha)
  have hcomp' :
      (∫ t in 0..alpha, sixVertexXiFourier lam (-t)) =
        ∫ t in -alpha..0, sixVertexXiFourier lam t := by
    simpa only [neg_zero] using hcomp
  unfold sixVertexRapidityMomentum
  rw [intervalIntegral.integral_symm, <- hcomp']
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact sixVertexXiFourier_neg lam t

private theorem projIcc_neg_pi_pi_neg (x : Real) :
    ((Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) (-x) :
        Set.Icc (-Real.pi) Real.pi) : Real) =
      -((Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x :
        Set.Icc (-Real.pi) Real.pi) : Real) := by
  simp only [Set.coe_projIcc]
  simp only [max_def, min_def]
  split_ifs <;> linarith [Real.pi_pos]

theorem sixVertexMomentumRapidity_neg
    {lam : Real} (hlam : 0 < lam) (x : Real) :
    sixVertexMomentumRapidity lam hlam (-x) =
      -sixVertexMomentumRapidity lam hlam x := by
  let hpi : -Real.pi <= Real.pi := by linarith [Real.pi_pos]
  let E := sixVertexRapidityMomentumOrderIso lam hlam
  let a : Set.Icc (-Real.pi) Real.pi :=
    Set.projIcc (-Real.pi) Real.pi hpi x
  let b : Set.Icc (-Real.pi) Real.pi :=
    Set.projIcc (-Real.pi) Real.pi hpi (-x)
  let u := E.symm a
  have hab : (b : Real) = -(a : Real) := by
    exact projIcc_neg_pi_pi_neg x
  have hnegMem : -(u : Real) ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [u.property.1, u.property.2]
  let uneg : Set.Icc (-Real.pi) Real.pi := ⟨-(u : Real), hnegMem⟩
  have heu : sixVertexRapidityMomentum lam (u : Real) = (a : Real) := by
    exact congrArg Subtype.val (E.apply_symm_apply a)
  have hsymm : E.symm b = uneg := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change (b : Real) = sixVertexRapidityMomentum lam (-(u : Real))
    rw [sixVertexRapidityMomentum_neg lam, heu, hab]
  unfold sixVertexMomentumRapidity
  change ((E.symm b : Set.Icc (-Real.pi) Real.pi) : Real) =
    -((E.symm a : Set.Icc (-Real.pi) Real.pi) : Real)
  rw [hsymm]

theorem odd_sixVertexContinuousOffsetFourier
    {c : Real} (hc : 2 < c) :
    Function.Odd (sixVertexContinuousOffsetFourier c hc) := by
  intro x
  unfold sixVertexContinuousOffsetFourier
  rw [sixVertexMomentumRapidity_neg
    (sixVertexAntiferroelectricLambda_pos hc),
    odd_sixVertexOffsetRapidityProfile]

theorem intervalIntegral_sin_nat_mul_mul_sin_nat_mul
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (∫ alpha in -Real.pi..Real.pi,
      Real.sin ((m : Real) * alpha) *
        Real.sin ((n : Real) * alpha)) =
      if m = n then Real.pi else 0 := by
  let zdiff : Int := (m : Int) - (n : Int)
  let zsum : Int := (m : Int) + (n : Int)
  have hsum : zsum ≠ 0 := by dsimp [zsum]; omega
  have hid (alpha : Real) :
      2 * (Real.sin ((m : Real) * alpha) *
        Real.sin ((n : Real) * alpha)) =
      Real.cos ((zdiff : Real) * alpha) -
        Real.cos ((zsum : Real) * alpha) := by
    rw [show (zdiff : Real) * alpha =
        (m : Real) * alpha - (n : Real) * alpha by
      dsimp [zdiff]
      push_cast
      ring,
      show (zsum : Real) * alpha =
        (m : Real) * alpha + (n : Real) * alpha by
      dsimp [zsum]
      push_cast
      ring,
      Real.cos_sub, Real.cos_add]
    ring
  have htwo :
      2 * (∫ alpha in -Real.pi..Real.pi,
        Real.sin ((m : Real) * alpha) * Real.sin ((n : Real) * alpha)) =
      (∫ alpha in -Real.pi..Real.pi,
        Real.cos ((zdiff : Real) * alpha)) -
      ∫ alpha in -Real.pi..Real.pi,
        Real.cos ((zsum : Real) * alpha) := by
    rw [<- intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_congr (fun alpha _ => hid alpha)]
    exact intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun alpha : Real =>
        Real.cos ((zdiff : Real) * alpha))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun alpha : Real =>
        Real.cos ((zsum : Real) * alpha))).intervalIntegrable _ _)
  rw [intervalIntegral_cos_int_mul zdiff,
    intervalIntegral_cos_int_mul zsum, if_neg hsum, sub_zero] at htwo
  by_cases hmn : m = n
  · rw [if_pos hmn]
    have hdiff : zdiff = 0 := by dsimp [zdiff]; omega
    rw [if_pos hdiff] at htwo
    linarith
  · rw [if_neg hmn]
    have hdiff : zdiff ≠ 0 := by dsimp [zdiff]; omega
    rw [if_neg hdiff] at htwo
    linarith

theorem intervalIntegral_linearOffset_mul_sin
    {m : Nat} (hm : 0 < m) :
    (∫ alpha in -Real.pi..Real.pi,
      (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha)) =
      (-1 : Real) ^ m / (m : Real) := by
  let M : Real := m
  let F : Real -> Real := fun alpha =>
    -(alpha * Real.cos (M * alpha)) / M +
      Real.sin (M * alpha) / M ^ 2
  have hM : M ≠ 0 := by dsimp [M]; exact_mod_cast hm.ne'
  have hderiv (alpha : Real) :
      HasDerivAt F (alpha * Real.sin (M * alpha)) alpha := by
    have hlin : HasDerivAt (fun x : Real => M * x) M alpha := by
      simpa using (hasDerivAt_id alpha).const_mul M
    have hcos := (Real.hasDerivAt_cos (M * alpha)).comp alpha hlin
    have hsin := (Real.hasDerivAt_sin (M * alpha)).comp alpha hlin
    have h := ((hasDerivAt_id alpha).mul hcos).neg.div_const M |>.add
      (hsin.div_const (M ^ 2))
    convert h using 1 <;>
      simp only [Function.comp_apply, id_eq] <;>
      field_simp [hM] <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -Real.pi) (b := Real.pi)
    (f := F) (f' := fun alpha => alpha * Real.sin (M * alpha))
    (fun alpha _ => hderiv alpha)
    ((by fun_prop : Continuous (fun alpha : Real =>
      alpha * Real.sin (M * alpha))).intervalIntegrable _ _)
  have hraw :
      (∫ alpha in -Real.pi..Real.pi,
        alpha * Real.sin ((m : Real) * alpha)) =
      -2 * Real.pi * ((-1 : Real) ^ m) / (m : Real) := by
    change (∫ alpha in -Real.pi..Real.pi,
      alpha * Real.sin (M * alpha)) = _
    rw [hFTC]
    dsimp [F, M]
    have hcosNeg : Real.cos (-(Real.pi * (m : Real))) = (-1 : Real) ^ m := by
      rw [Real.cos_neg]
      simpa [mul_comm] using Real.cos_nat_mul_pi m
    have hsinNeg : Real.sin (-(Real.pi * (m : Real))) = 0 := by
      rw [Real.sin_neg]
      simpa [mul_comm] using congrArg Neg.neg (Real.sin_nat_mul_pi m)
    have harg : (m : Real) * (-Real.pi) =
        -(Real.pi * (m : Real)) := by ring
    have hcosNeg' : Real.cos ((m : Real) * (-Real.pi)) =
        (-1 : Real) ^ m := by rw [harg, hcosNeg]
    have hsinNeg' : Real.sin ((m : Real) * (-Real.pi)) = 0 := by
      rw [harg, hsinNeg]
    rw [Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, hcosNeg', hsinNeg']
    simp only [zero_div, add_zero]
    field_simp
    ring
  rw [show (fun alpha : Real =>
      (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha)) =
      fun alpha => (-1 / (2 * Real.pi)) *
        (alpha * Real.sin ((m : Real) * alpha)) by
    funext alpha
    ring,
    intervalIntegral.integral_const_mul, hraw]
  field_simp [Real.pi_ne_zero]

private def offsetCorrectionMulSinContinuous
    (lam : Real) (n m : Nat) : C(Real, Real) :=
  ⟨fun alpha => sixVertexOffsetCorrectionTerm lam n alpha *
      Real.sin ((m : Real) * alpha), by
    unfold sixVertexOffsetCorrectionTerm
    fun_prop⟩

theorem intervalIntegral_offsetCorrectionTerm_mul_sin
    (lam : Real) (n : Nat) {m : Nat} (hm : 0 < m) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexOffsetCorrectionTerm lam n alpha *
        Real.sin ((m : Real) * alpha)) =
      if n + 1 = m then sixVertexGapCorrectionTerm lam n else 0 := by
  unfold sixVertexOffsetCorrectionTerm
  rw [show (fun alpha : Real =>
      (sixVertexGapCorrectionTerm lam n / Real.pi *
        Real.sin ((n + 1 : Real) * alpha)) *
          Real.sin ((m : Real) * alpha)) =
      fun alpha => (sixVertexGapCorrectionTerm lam n / Real.pi) *
        (Real.sin (((n + 1 : Nat) : Real) * alpha) *
          Real.sin ((m : Real) * alpha)) by
    funext alpha
    have hncast : (n + 1 : Real) = (((n + 1 : Nat) : Real)) := by
      norm_num
    rw [hncast]
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral_sin_nat_mul_mul_sin_nat_mul (by omega) hm]
  by_cases hnm : n + 1 = m
  · rw [if_pos hnm, if_pos hnm]
    field_simp [Real.pi_ne_zero]
  · rw [if_neg hnm, if_neg hnm, mul_zero]

theorem intervalIntegral_offsetCorrection_mul_sin
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m) :
    (∫ alpha in -Real.pi..Real.pi,
      (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
        Real.sin ((m : Real) * alpha)) =
      sixVertexGapCorrectionTerm lam (m - 1) := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  have hnorm : Summable (fun n : Nat =>
      ‖(offsetCorrectionMulSinContinuous lam n m).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (by positivity :
      0 <= (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1))]
    intro alpha
    change |sixVertexOffsetCorrectionTerm lam n (alpha : Real) *
      Real.sin ((m : Real) * alpha)| <= _
    rw [abs_mul]
    calc
      |sixVertexOffsetCorrectionTerm lam n alpha| *
          |Real.sin ((m : Real) * alpha)| <=
        ‖sixVertexOffsetCorrectionTerm lam n alpha‖ * 1 := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul (le_rfl)
            (abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
            (abs_nonneg _) (abs_nonneg _)
      _ <= (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by
        simpa only [mul_one] using
          norm_sixVertexOffsetCorrectionTerm_le lam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hseries :
      (∫ alpha in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      ∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
        sixVertexOffsetCorrectionTerm lam n alpha *
          Real.sin ((m : Real) * alpha) := by
    calc
      _ = ∫ alpha in -Real.pi..Real.pi,
          (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha *
            Real.sin ((m : Real) * alpha)) := by
        apply intervalIntegral.integral_congr
        intro alpha _
        exact tsum_mul_right.symm
      _ = _ := by
        simpa only [offsetCorrectionMulSinContinuous] using hswap.symm
  rw [hseries]
  simp_rw [intervalIntegral_offsetCorrectionTerm_mul_sin lam _ hm]
  have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [tsum_eq_single (m - 1)]
  · rw [if_pos hpred]
  · intro n hn
    rw [if_neg]
    intro hnm
    apply hn
    omega



theorem sixVertexOffsetRapidityProfile_sineCoefficient
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m) :
    (1 / Real.pi) *
        (∫ alpha in -Real.pi..Real.pi,
          sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((m : Real) * alpha)) =
      (-1 : Real) ^ m * Real.tanh ((m : Real) * lam) /
        (Real.pi * (m : Real)) := by
  have hlinear := intervalIntegral_linearOffset_mul_sin hm
  have hcorr := intervalIntegral_offsetCorrection_mul_sin hlam hm
  have hcorrCont : Continuous (fun alpha =>
      ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexOffsetCorrectionTerm
      fun_prop
    · have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
      have hq1 : Real.exp (-2 * lam) < 1 := by
        rw [<- Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      exact ((summable_geometric_of_lt_one hq0 hq1).comp_injective
        Nat.succ_injective).mul_left (2 / Real.pi)
    · intro n alpha
      exact norm_sixVertexOffsetCorrectionTerm_le lam n alpha
  have hsplit :
      (∫ alpha in -Real.pi..Real.pi,
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha) +
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      (∫ alpha in -Real.pi..Real.pi,
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha)) +
      ∫ alpha in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha) := by
    exact intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun alpha : Real =>
        (-alpha / (2 * Real.pi)) *
          Real.sin ((m : Real) * alpha))).intervalIntegrable _ _)
      ((hcorrCont.mul (by fun_prop : Continuous (fun alpha : Real =>
        Real.sin ((m : Real) * alpha)))).intervalIntegrable _ _)
  unfold sixVertexOffsetRapidityProfile
  rw [show (fun alpha : Real =>
      (-alpha / (2 * Real.pi) +
        ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha)) =
      fun alpha =>
        (-alpha / (2 * Real.pi)) * Real.sin ((m : Real) * alpha) +
        (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) *
          Real.sin ((m : Real) * alpha) by
    funext alpha
    ring]
  rw [hsplit, hlinear, hcorr]
  rw [sixVertexGapCorrectionTerm]
  have hpredNat : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpredReal : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
    exact_mod_cast hpredNat
  rw [hpredNat, hpredReal]
  field_simp [Real.pi_ne_zero, (by positivity : (m : Real) ≠ 0)]
  ring

end

end StatMech.FrontierD
