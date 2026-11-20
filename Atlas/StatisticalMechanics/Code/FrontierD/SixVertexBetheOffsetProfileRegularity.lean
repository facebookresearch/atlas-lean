/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuousOffsetFourier
import Mathlib.Topology.MetricSpace.Antilipschitz










namespace StatMech.FrontierD

noncomputable section

def sixVertexOffsetCorrectionLipschitzTerm
    (lam : Real) (n : Nat) : Real :=
  (2 / Real.pi) * (n + 1 : Real) *
    Real.exp (-2 * lam) ^ (n + 1)

theorem summable_sixVertexOffsetCorrectionLipschitzTerm
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexOffsetCorrectionLipschitzTerm lam) := by
  let q := Real.exp (-2 * lam)
  have hq0 : 0 <= q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hbase := summable_pow_mul_geometric_of_norm_lt_one
    (R := Real) 1 hqnorm
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hscaled := hsucc.mul_left (2 / Real.pi)
  exact hscaled.congr fun n => by
    change (2 / Real.pi) * (((n.succ : Nat) : Real) ^ 1 * q ^ n.succ) =
      (2 / Real.pi) * (n + 1 : Real) * q ^ (n + 1)
    simp only [pow_one, Nat.cast_succ, Nat.succ_eq_add_one]
    ring

theorem sixVertexOffsetCorrectionLipschitzTerm_nonneg
    (lam : Real) (n : Nat) :
    0 <= sixVertexOffsetCorrectionLipschitzTerm lam n := by
  unfold sixVertexOffsetCorrectionLipschitzTerm
  positivity

theorem abs_sixVertexOffsetCorrectionTerm_sub_le
    (lam : Real) (n : Nat) (alpha beta : Real) :
    |sixVertexOffsetCorrectionTerm lam n alpha -
        sixVertexOffsetCorrectionTerm lam n beta| <=
      sixVertexOffsetCorrectionLipschitzTerm lam n * |alpha - beta| := by
  let m : Real := n + 1
  have hm : 0 <= m := by dsimp [m]; positivity
  have hsin :
      |Real.sin (m * alpha) - Real.sin (m * beta)| <=
        m * |alpha - beta| := by
    calc
      |Real.sin (m * alpha) - Real.sin (m * beta)| <=
          |m * alpha - m * beta| := Real.abs_sin_sub_sin_le _ _
      _ = m * |alpha - beta| := by
        rw [show m * alpha - m * beta = m * (alpha - beta) by ring,
          abs_mul, abs_of_nonneg hm]
  have hcoeff := sixVertexGapCorrectionTerm_norm_le lam n
  rw [Real.norm_eq_abs] at hcoeff
  unfold sixVertexOffsetCorrectionTerm
    sixVertexOffsetCorrectionLipschitzTerm
  change |(sixVertexGapCorrectionTerm lam n / Real.pi) *
      Real.sin (m * alpha) -
    (sixVertexGapCorrectionTerm lam n / Real.pi) *
      Real.sin (m * beta)| <= _
  rw [<- mul_sub, abs_mul, abs_div, abs_of_pos Real.pi_pos]
  calc
    |sixVertexGapCorrectionTerm lam n| / Real.pi *
        |Real.sin (m * alpha) - Real.sin (m * beta)| <=
      (2 * Real.exp (-2 * lam) ^ (n + 1)) / Real.pi *
        (m * |alpha - beta|) :=
      mul_le_mul
        (div_le_div_of_nonneg_right hcoeff Real.pi_pos.le) hsin
        (abs_nonneg _) (by positivity)
    _ = (2 / Real.pi) * (n + 1 : Real) *
        Real.exp (-2 * lam) ^ (n + 1) * |alpha - beta| := by
      dsimp [m]
      ring

def sixVertexOffsetRapidityLipschitzBound (lam : Real) : Real :=
  1 / (2 * Real.pi) +
    ∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n

def sixVertexOffsetRapidityLipschitzNNReal (lam : Real) : NNReal :=
  Real.toNNReal (sixVertexOffsetRapidityLipschitzBound lam)

theorem sixVertexOffsetRapidityLipschitzBound_pos
    {lam : Real} (hlam : 0 < lam) :
    0 < sixVertexOffsetRapidityLipschitzBound lam := by
  unfold sixVertexOffsetRapidityLipschitzBound
  have hsum : 0 <= ∑' n : Nat,
      sixVertexOffsetCorrectionLipschitzTerm lam n :=
    tsum_nonneg (sixVertexOffsetCorrectionLipschitzTerm_nonneg lam)
  positivity

theorem lipschitzWith_sixVertexOffsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    LipschitzWith (sixVertexOffsetRapidityLipschitzNNReal lam)
      (sixVertexOffsetRapidityProfile lam) := by
  have hL : 0 <= sixVertexOffsetRapidityLipschitzBound lam :=
    (sixVertexOffsetRapidityLipschitzBound_pos hlam).le
  have hLcoe : (sixVertexOffsetRapidityLipschitzNNReal lam : Real) =
      sixVertexOffsetRapidityLipschitzBound lam := by
    exact Real.coe_toNNReal _ hL
  apply LipschitzWith.of_dist_le_mul
  intro alpha beta
  rw [Real.dist_eq, Real.dist_eq, hLcoe]
  have hAlpha := summable_sixVertexOffsetCorrectionTerm hlam alpha
  have hBeta := summable_sixVertexOffsetCorrectionTerm hlam beta
  have hDiff := hAlpha.sub hBeta
  have hMajor := summable_sixVertexOffsetCorrectionLipschitzTerm hlam
  have hMajorScaled := hMajor.mul_right |alpha - beta|
  have hcorr :
      |(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta| <=
        (∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n) *
          |alpha - beta| := by
    rw [<- hAlpha.tsum_sub hBeta, <- tsum_mul_right]
    calc
      |∑' n : Nat, (sixVertexOffsetCorrectionTerm lam n alpha -
          sixVertexOffsetCorrectionTerm lam n beta)| =
        ‖∑' n : Nat, (sixVertexOffsetCorrectionTerm lam n alpha -
          sixVertexOffsetCorrectionTerm lam n beta)‖ := by
            rw [Real.norm_eq_abs]
      _ <= ∑' n : Nat,
          ‖sixVertexOffsetCorrectionTerm lam n alpha -
            sixVertexOffsetCorrectionTerm lam n beta‖ :=
        norm_tsum_le_tsum_norm hDiff.norm
      _ <= ∑' n : Nat,
          sixVertexOffsetCorrectionLipschitzTerm lam n *
            |alpha - beta| := by
        apply hDiff.norm.tsum_le_tsum
        · intro n
          rw [Real.norm_eq_abs]
          exact abs_sixVertexOffsetCorrectionTerm_sub_le lam n alpha beta
        · exact hMajorScaled
  unfold sixVertexOffsetRapidityProfile
  have hlinear :
      |-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)| =
        (1 / (2 * Real.pi)) * |alpha - beta| := by
    have hneg : (-1 / (2 * Real.pi) : Real) <= 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    rw [show -alpha / (2 * Real.pi) - -beta / (2 * Real.pi) =
      (-1 / (2 * Real.pi)) * (alpha - beta) by ring,
      abs_mul, abs_of_nonpos hneg]
    ring
  calc
    |(-alpha / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
        (-beta / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta)| <=
      |-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)| +
        |(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta| := by
      rw [show (-alpha / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
        (-beta / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta) =
        (-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)) +
          ((∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
            ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta) by ring]
      exact abs_add_le _ _
    _ <= (1 / (2 * Real.pi)) * |alpha - beta| +
        (∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n) *
          |alpha - beta| := add_le_add hlinear.le hcorr
    _ = sixVertexOffsetRapidityLipschitzBound lam * |alpha - beta| := by
      unfold sixVertexOffsetRapidityLipschitzBound
      ring

def sixVertexRapidityMomentumDerivativeFloor (lam : Real) : Real :=
  Real.sinh lam / (Real.cosh lam + 1)

theorem sixVertexRapidityMomentumDerivativeFloor_pos
    {lam : Real} (hlam : 0 < lam) :
    0 < sixVertexRapidityMomentumDerivativeFloor lam := by
  unfold sixVertexRapidityMomentumDerivativeFloor
  exact div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)

theorem sixVertexRapidityMomentumDerivativeFloor_le
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexRapidityMomentumDerivativeFloor lam <=
      sixVertexXiFourier lam alpha := by
  rw [sixVertexXiFourier_eq hlam]
  unfold sixVertexRapidityMomentumDerivativeFloor
  have hsinh : 0 < Real.sinh lam := Real.sinh_pos_iff.mpr hlam
  have hden : 0 < Real.cosh lam - Real.cos alpha := by
    have hc : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hupper : Real.cosh lam - Real.cos alpha <= Real.cosh lam + 1 := by
    linarith [Real.neg_one_le_cos alpha]
  exact div_le_div_of_nonneg_left hsinh.le hden hupper

def sixVertexMomentumRapidityLipschitzNNReal
    (lam : Real) : NNReal :=
  Real.toNNReal (1 / sixVertexRapidityMomentumDerivativeFloor lam)

theorem lipschitzWith_sixVertexMomentumRapidity
    {lam : Real} (hlam : 0 < lam) :
    LipschitzWith (sixVertexMomentumRapidityLipschitzNNReal lam)
      (sixVertexMomentumRapidity lam hlam) := by
  let floor := sixVertexRapidityMomentumDerivativeFloor lam
  have hfloor : 0 < floor := sixVertexRapidityMomentumDerivativeFloor_pos hlam
  have hK : 0 <= 1 / floor := by positivity
  have hKcoe : (sixVertexMomentumRapidityLipschitzNNReal lam : Real) =
      1 / floor := by
    exact Real.coe_toNNReal _ hK
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let px := (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x : Real)
  let py := (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y : Real)
  let alpha := sixVertexMomentumRapidity lam hlam x
  let beta := sixVertexMomentumRapidity lam hlam y
  have hpx : px ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [px]
    exact (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x).property
  have hpy : py ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [py]
    exact (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y).property
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x)).property
  have hbeta : beta ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [beta, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y)).property
  have hkalpha : sixVertexRapidityMomentum lam alpha = px := by
    dsimp [alpha, px, sixVertexMomentumRapidity]
    exact congrArg Subtype.val
      ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply _)
  have hkbeta : sixVertexRapidityMomentum lam beta = py := by
    dsimp [beta, py, sixVertexMomentumRapidity]
    exact congrArg Subtype.val
      ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply _)
  have hdiff : Differentiable Real (sixVertexRapidityMomentum lam) :=
    fun z => (hasDerivAt_sixVertexRapidityMomentum hlam z).differentiableAt
  have hrapidity : |alpha - beta| <= (1 / floor) * |px - py| := by
    rcases le_total alpha beta with hab | hba
    · have hgrowth := (convex_Icc alpha beta).mul_sub_le_image_sub_of_le_deriv
          (continuous_iff_continuousAt.2 fun z =>
            (hasDerivAt_sixVertexRapidityMomentum hlam z).continuousAt).continuousOn
          hdiff.differentiableOn
          (fun z _ => by
            rw [(hasDerivAt_sixVertexRapidityMomentum hlam z).deriv]
            exact sixVertexRapidityMomentumDerivativeFloor_le hlam z)
          alpha (Set.left_mem_Icc.mpr hab) beta
          (Set.right_mem_Icc.mpr hab) hab
      rw [hkalpha, hkbeta] at hgrowth
      have hp : px <= py := by
        rw [<- hkalpha, <- hkbeta]
        exact (strictMono_sixVertexRapidityMomentum hlam).monotone hab
      have hmain : beta - alpha <= (1 / floor) * (py - px) := by
        calc
        beta - alpha <= (py - px) / floor :=
          (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hgrowth)
        _ = (1 / floor) * (py - px) := by ring
      simpa [abs_of_nonpos (sub_nonpos.mpr hab),
        abs_of_nonpos (sub_nonpos.mpr hp)] using hmain
    · have hgrowth := (convex_Icc beta alpha).mul_sub_le_image_sub_of_le_deriv
          (continuous_iff_continuousAt.2 fun z =>
            (hasDerivAt_sixVertexRapidityMomentum hlam z).continuousAt).continuousOn
          hdiff.differentiableOn
          (fun z _ => by
            rw [(hasDerivAt_sixVertexRapidityMomentum hlam z).deriv]
            exact sixVertexRapidityMomentumDerivativeFloor_le hlam z)
          beta (Set.left_mem_Icc.mpr hba) alpha
          (Set.right_mem_Icc.mpr hba) hba
      rw [hkalpha, hkbeta] at hgrowth
      have hp : py <= px := by
        rw [<- hkalpha, <- hkbeta]
        exact (strictMono_sixVertexRapidityMomentum hlam).monotone hba
      rw [abs_of_nonneg (sub_nonneg.mpr hba),
        abs_of_nonneg (sub_nonneg.mpr hp)]
      calc
        alpha - beta <= (px - py) / floor :=
          (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hgrowth)
        _ = (1 / floor) * (px - py) := by ring
  have hproj := (LipschitzWith.projIcc
    (by linarith [Real.pi_pos] : -Real.pi <= Real.pi)).dist_le_mul x y
  have hproj' : |px - py| <= |x - y| := by
    simpa [px, py, Real.dist_eq] using hproj
  rw [Real.dist_eq, Real.dist_eq, hKcoe]
  exact hrapidity.trans (mul_le_mul_of_nonneg_left hproj' hK)

def sixVertexContinuousOffsetFourierLipschitzNNReal
    (c : Real) : NNReal :=
  sixVertexMomentumRapidityLipschitzNNReal
      (sixVertexAntiferroelectricLambda c) *
    sixVertexOffsetRapidityLipschitzNNReal
      (sixVertexAntiferroelectricLambda c)

theorem lipschitzWith_sixVertexContinuousOffsetFourier
    {c : Real} (hc : 2 < c) :
    LipschitzWith (sixVertexContinuousOffsetFourierLipschitzNNReal c)
      (sixVertexContinuousOffsetFourier c hc) := by
  simpa [sixVertexContinuousOffsetFourierLipschitzNNReal,
      sixVertexContinuousOffsetFourier, Function.comp_def, mul_comm] using
    (lipschitzWith_sixVertexOffsetRapidityProfile
        (sixVertexAntiferroelectricLambda_pos hc)).comp
      (lipschitzWith_sixVertexMomentumRapidity
        (sixVertexAntiferroelectricLambda_pos hc))

end

end StatMech.FrontierD
