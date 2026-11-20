/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
import Code.FrontierD.SixVertexBetheOffsetLogSingularity
import Code.FrontierD.SixVertexBetheOffsetProfileRegularity





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexRegularizedBetheLogNormDerivative
    (c epsilon x : Real) : Real :=
  let a := c ^ 2 - 1
  (-a * Real.sin x / (a ^ 2 + 1 + 2 * a * Real.cos x)) -
    Real.sin x / (2 - 2 * Real.cos x + epsilon)

theorem hasDerivAt_sixVertexRegularizedBetheLogKernel
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    HasDerivAt (sixVertexRegularizedBetheLogKernel c epsilon)
      (sixVertexRegularizedBetheLogNormDerivative c epsilon x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real -> Real := fun y => 2 - 2 * Real.cos y + epsilon
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add (a ^ 2 + 1)
      using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add (2 + epsilon)
      using 1
    · funext y
      dsimp [B]
      ring
    · ring
  have h := ((hAderiv.log hA.ne').sub (hBderiv.log hB.ne')).const_mul
    (1 / 2 : Real)
  unfold sixVertexRegularizedBetheLogKernel
    sixVertexBetheLogNumerator sixVertexBetheLogDenominator
    sixVertexRegularizedBetheLogNormDerivative
  dsimp [a, A, B] at h ⊢
  convert h using 1 <;> field_simp [hA.ne', hB.ne'] <;> ring

def sixVertexRegularizedRapidityLogDerivativeTerm
    (lam epsilon : Real) (n : Nat) (alpha : Real) : Real :=
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  (q ^ (n + 1) - r ^ (n + 1)) *
    Real.sin ((n + 1 : Real) * alpha)

def sixVertexRegularizedRapidityLogDerivative
    (lam epsilon alpha : Real) : Real :=
  ∑' n : Nat,
    sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha

private theorem summable_rapidityLogDerivative_majorant
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    Summable (fun n : Nat =>
      sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
        sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)) := by
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  exact ((summable_geometric_of_lt_one hq.1.le hq.2).comp_injective
      Nat.succ_injective).add
    ((summable_geometric_of_lt_one hr.1.le hr.2).comp_injective
      Nat.succ_injective)

theorem summable_sixVertexRegularizedRapidityLogDerivativeTerm
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    Summable (fun n : Nat =>
      sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha) := by
  apply (summable_rapidityLogDerivative_majorant hlam hepsilon).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  unfold sixVertexRegularizedRapidityLogDerivativeTerm
  dsimp only
  rw [abs_mul]
  have hqpow : 0 <= sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) :=
    pow_nonneg (sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam).1.le _
  have hrpow : 0 <=
      sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1) :=
    pow_nonneg
      (sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon).1.le _
  have hdiff :
      |sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) -
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)| <=
        sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1) := by
    simpa [abs_of_nonneg hqpow, abs_of_nonneg hrpow] using
      (abs_sub (sixVertexFreeEnergyRapidityRadius lam ^ (n + 1))
        (sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)))
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) -
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)| *
        |Real.sin ((n + 1 : Real) * alpha)| <=
        (sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)) * 1 :=
      mul_le_mul hdiff hsin (abs_nonneg _) (add_nonneg hqpow hrpow)
    _ = _ := mul_one _

private theorem hasDerivAt_sixVertexLogCosineSeries
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    HasDerivAt (sixVertexLogCosineSeries r)
      (∑' n : Nat, -r ^ (n + 1) *
        Real.sin ((n + 1 : Real) * alpha)) alpha := by
  let g : Nat -> Real -> Real := fun n x =>
    r ^ (n + 1) * Real.cos ((n + 1 : Real) * x) / (n + 1 : Real)
  let g' : Nat -> Real -> Real := fun n x =>
    -r ^ (n + 1) * Real.sin ((n + 1 : Real) * x)
  let u : Nat -> Real := fun n => |r| ^ (n + 1)
  have hu : Summable u :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  have hg (n : Nat) (x : Real) : HasDerivAt (g n) (g' n x) x := by
    have hlin : HasDerivAt (fun y : Real => (n + 1 : Real) * y)
        (n + 1 : Real) x := by
      simpa using (hasDerivAt_id x).const_mul (n + 1 : Real)
    have h := ((Real.hasDerivAt_cos ((n + 1 : Real) * x)).comp x hlin).const_mul
      (r ^ (n + 1) / (n + 1 : Real))
    have hm : (n + 1 : Real) ≠ 0 := by positivity
    convert h using 1
    · funext y
      dsimp [g]
      ring
    · dsimp [g']
      field_simp [hm]
  have hg' (n : Nat) (x : Real) : ‖g' n x‖ <= u n := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
    have hs : |Real.sin ((n + 1 : Real) * x)| <= 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (pow_nonneg (abs_nonneg r) _)
  have hg0 : Summable (fun n => g n 0) := by
    apply hu.of_norm_bounded
    intro n
    dsimp [g, u]
    rw [mul_zero, Real.cos_zero, mul_one]
    have hden : 1 <= |(n + 1 : Real)| := by
      rw [abs_of_pos (by positivity)]
      norm_num
    calc
      |r ^ (n + 1) / (n + 1 : Real)| =
          |r ^ (n + 1)| / |(n + 1 : Real)| := abs_div _ _
      _ = |r| ^ (n + 1) / |(n + 1 : Real)| := by rw [abs_pow]
      _ <= |r| ^ (n + 1) :=
        div_le_self (pow_nonneg (abs_nonneg r) _) hden
  have h := hasDerivAt_tsum (u := u) (g := g) (g' := g')
    hu hg hg' hg0 alpha
  change HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n alpha) alpha
  exact h

private theorem summable_logCosineDerivative
    {r : Real} (hr : r ∈ Set.Ioo 0 1) (alpha : Real) :
    Summable (fun n : Nat => -r ^ (n + 1) *
      Real.sin ((n + 1 : Real) * alpha)) := by
  have hgeom := (summable_geometric_of_lt_one hr.1.le hr.2).comp_injective
    Nat.succ_injective
  apply hgeom.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hr.1.le _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_one _) (pow_nonneg hr.1.le _)

theorem hasDerivAt_sixVertexRegularizedRapidityLogSeries
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    HasDerivAt
      (fun beta =>
        sixVertexRegularizedRapidityConstant lam epsilon +
          sixVertexLogCosineSeries
            (sixVertexRegularizedRapidityRadius lam epsilon) beta -
          sixVertexLogCosineSeries
            (sixVertexFreeEnergyRapidityRadius lam) beta)
      (sixVertexRegularizedRapidityLogDerivative lam epsilon alpha) alpha := by
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hR := hasDerivAt_sixVertexLogCosineSeries
    (by rw [abs_of_pos hr.1]; exact hr.2) alpha
  have hQ := hasDerivAt_sixVertexLogCosineSeries
    (by rw [abs_of_pos hq.1]; exact hq.2) alpha
  have h := (hR.const_add
    (sixVertexRegularizedRapidityConstant lam epsilon)).sub hQ
  convert h using 1
  unfold sixVertexRegularizedRapidityLogDerivative
    sixVertexRegularizedRapidityLogDerivativeTerm
  have hRsum := summable_logCosineDerivative hr alpha
  have hQsum := summable_logCosineDerivative hq alpha
  rw [<- hRsum.tsum_sub hQsum]
  apply tsum_congr
  intro n
  ring

theorem sixVertexRegularizedBetheLogDerivative_rapidityMomentum
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexRegularizedBetheLogNormDerivative c epsilon
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) *
      sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha =
    sixVertexRegularizedRapidityLogDerivative
      (sixVertexAntiferroelectricLambda c) epsilon alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hleft := (hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon).comp
    alpha (hasDerivAt_sixVertexRapidityMomentum hlam alpha)
  have hright := hasDerivAt_sixVertexRegularizedRapidityLogSeries
    hlam hepsilon alpha
  have hfun : (fun beta => sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexRapidityMomentum lam beta)) =
      fun beta =>
        sixVertexRegularizedRapidityConstant lam epsilon +
          sixVertexLogCosineSeries
            (sixVertexRegularizedRapidityRadius lam epsilon) beta -
          sixVertexLogCosineSeries
            (sixVertexFreeEnergyRapidityRadius lam) beta := by
    funext beta
    exact sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
      hc hepsilon beta
  change HasDerivAt
    (fun beta => sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexRapidityMomentum lam beta)) _ alpha at hleft
  rw [hfun] at hleft
  exact hright.unique hleft |>.symm

def sixVertexOffsetLogFourierDampedTerm
    (lam r : Real) (n : Nat) : Real :=
  (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
    (sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) - r ^ (n + 1)) /
      (n + 1 : Real)

def sixVertexOffsetLogFourierDampedValue (lam r : Real) : Real :=
  ∑' n : Nat, sixVertexOffsetLogFourierDampedTerm lam r n

private def regularizedRapidityLogDerivativeMulOffsetContinuous
    (lam epsilon : Real) (hlam : 0 < lam) (n : Nat) : C(Real, Real) :=
  ⟨fun alpha =>
      sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
        sixVertexOffsetRapidityProfile lam alpha,
    by
      apply Continuous.mul
      · unfold sixVertexRegularizedRapidityLogDerivativeTerm
        fun_prop
      · exact continuous_sixVertexOffsetRapidityProfile hlam⟩

theorem intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexRegularizedRapidityLogDerivative lam epsilon alpha *
        sixVertexOffsetRapidityProfile lam alpha) =
      sixVertexOffsetLogFourierDampedValue lam
        (sixVertexRegularizedRapidityRadius lam epsilon) := by
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  let L := (sixVertexOffsetRapidityLipschitzNNReal lam : Real) * Real.pi
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hL : 0 <= L := by dsimp [L]; positivity
  have hprofile (alpha : Real)
      (halpha : alpha ∈ Set.uIcc (-Real.pi) Real.pi) :
      |sixVertexOffsetRapidityProfile lam alpha| <= L := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at halpha
    have hlip := (lipschitzWith_sixVertexOffsetRapidityProfile hlam).dist_le_mul
      alpha 0
    have hzero : sixVertexOffsetRapidityProfile lam 0 = 0 := by
      simp [sixVertexOffsetRapidityProfile, sixVertexOffsetCorrectionTerm]
    rw [Real.dist_eq, Real.dist_eq, hzero, sub_zero, sub_zero] at hlip
    exact hlip.trans (mul_le_mul_of_nonneg_left (abs_le.2 halpha)
      (NNReal.coe_nonneg _))
  have hmajor : Summable (fun n : Nat =>
      (q ^ (n + 1) + r ^ (n + 1)) * L) :=
    ((summable_rapidityLogDerivative_majorant hlam hepsilon).mul_right L)
  have hnorm : Summable (fun n : Nat =>
      ‖(regularizedRapidityLogDerivativeMulOffsetContinuous
        lam epsilon hlam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (mul_nonneg
      (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _)) hL)]
    intro alpha
    change |sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n
      (alpha : Real) * sixVertexOffsetRapidityProfile lam alpha| <= _
    rw [abs_mul]
    have hterm :
        |sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha| <=
          q ^ (n + 1) + r ^ (n + 1) := by
      unfold sixVertexRegularizedRapidityLogDerivativeTerm
      dsimp only [q, r]
      rw [abs_mul]
      have hdiff : |q ^ (n + 1) - r ^ (n + 1)| <=
          q ^ (n + 1) + r ^ (n + 1) := by
        have h := abs_sub (q ^ (n + 1)) (r ^ (n + 1))
        rw [abs_pow, abs_pow, abs_of_pos hq.1, abs_of_pos hr.1] at h
        exact h
      simpa only [mul_one, q, r] using mul_le_mul hdiff (Real.abs_sin_le_one _)
        (abs_nonneg _) (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _))
    exact mul_le_mul hterm (hprofile alpha alpha.property)
      (abs_nonneg _) (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _))
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have htermIntegral (n : Nat) :
      (∫ alpha in -Real.pi..Real.pi,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha) =
        sixVertexOffsetLogFourierDampedTerm lam r n := by
    have hsine := sixVertexOffsetRapidityProfile_sineCoefficient hlam
      (show 0 < n + 1 by omega)
    have hsine' :
        (∫ alpha in -Real.pi..Real.pi,
          sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((n + 1 : Real) * alpha)) =
          (-1 : Real) ^ (n + 1) *
            Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real) := by
      have hm : (n + 1 : Real) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero] at hsine
      apply (eq_div_iff hm).2
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hsine
    unfold sixVertexRegularizedRapidityLogDerivativeTerm
      sixVertexOffsetLogFourierDampedTerm
    dsimp only [q, r]
    rw [show (fun alpha : Real =>
        (q ^ (n + 1) - r ^ (n + 1)) *
          Real.sin ((n + 1 : Real) * alpha) *
            sixVertexOffsetRapidityProfile lam alpha) =
        fun alpha => (q ^ (n + 1) - r ^ (n + 1)) *
          (sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((n + 1 : Real) * alpha)) by
      funext alpha; ring,
      intervalIntegral.integral_const_mul, hsine']
    ring
  unfold sixVertexRegularizedRapidityLogDerivative
    sixVertexOffsetLogFourierDampedValue
  rw [show (fun alpha : Real =>
      (∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha) *
          sixVertexOffsetRapidityProfile lam alpha) =
      fun alpha => ∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha by
    funext alpha
    exact tsum_mul_right.symm]
  calc
    (∫ alpha in -Real.pi..Real.pi, ∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha) =
        ∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
          sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
            sixVertexOffsetRapidityProfile lam alpha := by
      simpa [regularizedRapidityLogDerivativeMulOffsetContinuous] using hswap.symm
    _ = ∑' n : Nat, sixVertexOffsetLogFourierDampedTerm lam r n := by
      apply tsum_congr
      exact htermIntegral

def sixVertexOffsetLogFourierQTerm (lam : Real) (n : Nat) : Real :=
  (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
    sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) / (n + 1 : Real)

def sixVertexOffsetLogFourierQValue (lam : Real) : Real :=
  ∑' n : Nat, sixVertexOffsetLogFourierQTerm lam n

theorem summable_sixVertexOffsetLogFourierQTerm
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexOffsetLogFourierQTerm lam) := by
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hgeom := (summable_geometric_of_lt_one hq.1.le hq.2).comp_injective
    Nat.succ_injective
  apply hgeom.of_norm_bounded
  intro n
  unfold sixVertexOffsetLogFourierQTerm
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, abs_pow, abs_of_pos (by positivity : (0 : Real) < n + 1)]
  rw [abs_of_pos hq.1]
  have htanh : |Real.tanh ((n + 1 : Real) * lam)| <= 1 :=
    (abs_lt.2 ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le
  have hden : 1 <= (n + 1 : Real) := by norm_num
  have hpow : 0 <= sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) :=
    pow_nonneg hq.1.le _
  have hnum : 1 * |Real.tanh ((n + 1 : Real) * lam)| *
      sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) <=
      1 * 1 * sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htanh (by norm_num)) hpow
  calc
    1 * |Real.tanh ((n + 1 : Real) * lam)| *
          sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) /
          (n + 1 : Real) <=
        1 * 1 * sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) /
          (n + 1 : Real) := div_le_div_of_nonneg_right hnum (by positivity)
    _ <= 1 * 1 * sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) / 1 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) := by ring

theorem sixVertexOffsetLogFourierQTerm_add_correction
    (lam : Real) (n : Nat) :
    sixVertexOffsetLogFourierQTerm lam n +
      sixVertexGapCorrectionTerm lam n =
      -((-1 : Real) ^ (n + 1) *
        sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) / (n + 1 : Real)) := by
  let m : Real := n + 1
  let q : Real := Real.exp (-2 * m * lam)
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hden : 1 + q ≠ 0 := by positivity
  have hqpow : sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) = q := by
    unfold sixVertexFreeEnergyRapidityRadius
    rw [<- Real.exp_nat_mul]
    dsimp [m, q]
    push_cast
    congr 1
    ring
  rw [sixVertexOffsetLogFourierQTerm, sixVertexGapCorrectionTerm, hqpow]
  have htanh := tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div (m * lam)
  have hexp : Real.exp (-2 * (m * lam)) = q := by dsimp [q]; congr 1 <;> ring
  rw [hexp] at htanh
  have hcore : Real.tanh (m * lam) * (1 + q) = 1 - q := by
    field_simp [hden] at htanh ⊢
    nlinarith
  change (-1 : Real) ^ (n + 1) * Real.tanh (m * lam) * q / m +
      (-1 : Real) ^ (n + 1) * (Real.tanh (m * lam) - 1) / m = _
  field_simp [hm]
  dsimp [m] at hcore ⊢
  ring_nf at hcore ⊢
  nlinarith

theorem sixVertexOffsetLogFourierQValue_eq
    {lam : Real} (hlam : 0 < lam) :
    sixVertexOffsetLogFourierQValue lam =
      Real.log (1 + sixVertexFreeEnergyRapidityRadius lam) -
        ∑' n : Nat, sixVertexGapCorrectionTerm lam n := by
  let q := sixVertexFreeEnergyRapidityRadius lam
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hqAbs : |-q| < 1 := by rw [abs_neg, abs_of_pos hq.1]; exact hq.2
  have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one hqAbs).neg
  have hlog' : HasSum (fun n : Nat =>
      -((-1 : Real) ^ (n + 1) * q ^ (n + 1) / (n + 1 : Real)))
      (Real.log (1 + q)) := by
    convert hlog using 1
    · funext n
      rw [neg_pow]
      ring
    · congr 2
      ring
  have hQ := summable_sixVertexOffsetLogFourierQTerm hlam
  have hC := summable_sixVertexGapCorrectionTerm hlam
  have hadd := hQ.tsum_add hC
  have hsum : (∑' n : Nat, (
      sixVertexOffsetLogFourierQTerm lam n +
        sixVertexGapCorrectionTerm lam n)) = Real.log (1 + q) := by
    calc
      (∑' n : Nat, (sixVertexOffsetLogFourierQTerm lam n +
          sixVertexGapCorrectionTerm lam n)) =
          ∑' n : Nat, (-((-1 : Real) ^ (n + 1) * q ^ (n + 1) /
            (n + 1 : Real))) := by
        apply tsum_congr
        intro n
        exact sixVertexOffsetLogFourierQTerm_add_correction lam n
      _ = Real.log (1 + q) := hlog'.tsum_eq
  rw [hsum] at hadd
  unfold sixVertexOffsetLogFourierQValue
  dsimp [q] at hadd ⊢
  linarith

theorem sixVertexOffsetLogFourierQValue_sub_gapSeries
    {lam : Real} (hlam : 0 < lam) :
    sixVertexOffsetLogFourierQValue lam - sixVertexGapSeries lam =
      Real.log (Real.cosh lam) -
        sixVertexAntiferroelectricGapRate lam := by
  have hQ := sixVertexOffsetLogFourierQValue_eq hlam
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hOneq : 0 < 1 + sixVertexFreeEnergyRapidityRadius lam :=
    add_pos_of_pos_of_nonneg zero_lt_one hq.1.le
  have hcosh : Real.cosh lam =
      Real.exp lam * (1 + sixVertexFreeEnergyRapidityRadius lam) / 2 := by
    unfold sixVertexFreeEnergyRapidityRadius
    rw [Real.cosh_eq]
    have hneg : Real.exp (-lam) = Real.exp lam * Real.exp (-2 * lam) := by
      rw [<- Real.exp_add]
      congr 1
      ring
    rw [hneg]
    ring
  have hlogcosh : Real.log (Real.cosh lam) =
      lam + Real.log (1 + sixVertexFreeEnergyRapidityRadius lam) -
        Real.log 2 := by
    rw [hcosh, Real.log_div (mul_ne_zero (Real.exp_ne_zero _)
        hOneq.ne') (by norm_num),
      Real.log_mul (Real.exp_ne_zero _) hOneq.ne', Real.log_exp]
  rw [hQ, hlogcosh]
  unfold sixVertexAntiferroelectricGapRate sixVertexGapSeries
  ring

private theorem summable_gapSeriesTerm_mul_pow
    (lam : Real) {r : Real} (hr : |r| < 1) :
    Summable (fun n : Nat => sixVertexGapSeriesTerm lam n * r ^ n) := by
  have hgeom : Summable (fun n : Nat => |r| ^ n) :=
    summable_geometric_of_lt_one (abs_nonneg r) hr
  apply hgeom.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have htanh : |Real.tanh ((n + 1 : Real) * lam)| <= 1 :=
    (abs_lt.2 ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le
  have hm : 1 <= (n + 1 : Real) := by norm_num
  have hgap : |sixVertexGapSeriesTerm lam n| <= 1 := by
    unfold sixVertexGapSeriesTerm
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0 : Real) < n + 1)]
    calc
      1 * |Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real) <=
          1 * 1 / 1 := by gcongr
      _ = 1 := by norm_num
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hgap (pow_nonneg (abs_nonneg r) n)

theorem sixVertexOffsetLogFourierDampedValue_eq
    {lam : Real} (hlam : 0 < lam) {r : Real} (hr : r ∈ Set.Ioo 0 1) :
    sixVertexOffsetLogFourierDampedValue lam r =
      sixVertexOffsetLogFourierQValue lam -
        r * ∑' n : Nat, sixVertexGapSeriesTerm lam n * r ^ n := by
  have hQ := summable_sixVertexOffsetLogFourierQTerm hlam
  have hP := summable_gapSeriesTerm_mul_pow lam
    (by rw [abs_of_pos hr.1]; exact hr.2)
  have hrP : Summable (fun n : Nat =>
      r * (sixVertexGapSeriesTerm lam n * r ^ n)) := hP.mul_left r
  unfold sixVertexOffsetLogFourierDampedValue
    sixVertexOffsetLogFourierQValue
  rw [← tsum_mul_left]
  rw [← hQ.tsum_sub hrP]
  apply tsum_congr
  intro n
  unfold sixVertexOffsetLogFourierDampedTerm
    sixVertexOffsetLogFourierQTerm sixVertexGapSeriesTerm
  field_simp [(by positivity : (n + 1 : Real) ≠ 0)]
  ring

theorem tendsto_sixVertexOffsetLogFourierDampedValue
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexOffsetLogFourierDampedValue lam)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (Real.log (Real.cosh lam) -
        sixVertexAntiferroelectricGapRate lam)) := by
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (sixVertexGapSeries_partialSum_tendsto hlam)
  have hid : Tendsto (fun r : Real => r) (nhdsWithin 1 (Set.Iio 1))
      (nhds 1) := tendsto_id.mono_left inf_le_left
  have hprod := hid.mul hAbel
  have hconst : Tendsto (fun _ : Real => sixVertexOffsetLogFourierQValue lam)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (sixVertexOffsetLogFourierQValue lam)) := tendsto_const_nhds
  have hlim := hconst.sub hprod
  rw [one_mul, sixVertexOffsetLogFourierQValue_sub_gapSeries hlam] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  exact (sixVertexOffsetLogFourierDampedValue_eq hlam hr).symm

theorem tendsto_sixVertexOffsetLogFourierDampedValue_regularization
    {lam : Real} (hlam : 0 < lam) {iota : Type*} {l : Filter iota}
    {epsilon : iota -> Real} (hepsilon : Tendsto epsilon l (nhds 0))
    (hepsilonPos : ∀ᶠ i in l, 0 < epsilon i) :
    Tendsto (fun i => sixVertexOffsetLogFourierDampedValue lam
        (sixVertexRegularizedRapidityRadius lam (epsilon i))) l
      (nhds (Real.log (Real.cosh lam) -
        sixVertexAntiferroelectricGapRate lam)) := by
  apply (tendsto_sixVertexOffsetLogFourierDampedValue hlam).comp
  apply tendsto_nhdsWithin_iff.2
  refine ⟨tendsto_sixVertexRegularizedRapidityRadius
    hepsilon hepsilonPos hlam, ?_⟩
  filter_upwards [hepsilonPos] with i hi
  exact (sixVertexRegularizedRapidityRadius_mem_Ioo hlam hi).2

theorem intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    (∫ x in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogNormDerivative c epsilon x *
        sixVertexContinuousOffsetFourier c hc x) =
      sixVertexOffsetLogFourierDampedValue
        (sixVertexAntiferroelectricLambda c)
        (sixVertexRegularizedRapidityRadius
          (sixVertexAntiferroelectricLambda c) epsilon) := by
  let lam := sixVertexAntiferroelectricLambda c
  let k := sixVertexRapidityMomentum lam
  let g : Real -> Real := fun x =>
    sixVertexRegularizedBetheLogNormDerivative c epsilon x *
      sixVertexContinuousOffsetFourier c hc x
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hderivCont : Continuous
      (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
    unfold sixVertexRegularizedBetheLogNormDerivative
    have hA (x : Real) :
        (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x ≠ 0 := by
      have ha : 1 < c ^ 2 - 1 := by nlinarith
      nlinarith [Real.neg_one_le_cos x, sq_pos_of_pos (sub_pos.mpr ha)]
    have hB (x : Real) : 2 - 2 * Real.cos x + epsilon ≠ 0 := by
      nlinarith [Real.cos_le_one x]
    fun_prop
  have hg : Continuous g :=
    hderivCont.mul (continuous_sixVertexContinuousOffsetFourier hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi) (f := k)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun alpha _ => hasDerivAt_sixVertexRapidityMomentum hlam alpha)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  dsimp [k] at hsubst
  rw [sixVertexRapidityMomentum_neg_pi hlam,
    sixVertexRapidityMomentum_pi hlam] at hsubst
  have hpull :
      (∫ alpha in -Real.pi..Real.pi,
        (g ∘ k) alpha * sixVertexXiFourier lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        sixVertexRegularizedRapidityLogDerivative lam epsilon alpha *
          sixVertexOffsetRapidityProfile lam alpha := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at halpha
    dsimp only [Function.comp_apply, g, k]
    rw [show sixVertexRegularizedBetheLogNormDerivative c epsilon
          (sixVertexRapidityMomentum lam alpha) *
          sixVertexContinuousOffsetFourier c hc
            (sixVertexRapidityMomentum lam alpha) *
              sixVertexXiFourier lam alpha =
        (sixVertexRegularizedBetheLogNormDerivative c epsilon
          (sixVertexRapidityMomentum lam alpha) *
            sixVertexXiFourier lam alpha) *
          sixVertexContinuousOffsetFourier c hc
            (sixVertexRapidityMomentum lam alpha) by ring]
    dsimp [lam]
    rw [sixVertexRegularizedBetheLogDerivative_rapidityMomentum hc hepsilon,
      sixVertexContinuousOffsetFourier_rapidityMomentum hc halpha]
  change (∫ x in -Real.pi..Real.pi, g x) = _
  calc
    (∫ x in -Real.pi..Real.pi, g x) =
        ∫ alpha in -Real.pi..Real.pi,
          g (sixVertexRapidityMomentum lam alpha) *
            sixVertexXiFourier lam alpha := hsubst.symm
    _ = ∫ alpha in -Real.pi..Real.pi,
        sixVertexRegularizedRapidityLogDerivative lam epsilon alpha *
          sixVertexOffsetRapidityProfile lam alpha := by
      simpa [k, Function.comp_def] using hpull
    _ = _ := intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset
      hlam hepsilon

theorem continuous_sixVertexRegularizedBetheLogNormDerivative
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    Continuous (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
  unfold sixVertexRegularizedBetheLogNormDerivative
  have hA (x : Real) :
      (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x ≠ 0 := by
    have ha : 1 < c ^ 2 - 1 := by nlinarith
    nlinarith [Real.neg_one_le_cos x, sq_pos_of_pos (sub_pos.mpr ha)]
  have hB (x : Real) : 2 - 2 * Real.cos x + epsilon ≠ 0 := by
    nlinarith [Real.cos_le_one x]
  fun_prop

theorem abs_mul_sixVertexRegularizedBetheLogNormDerivative_le
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hx : x ≠ 0) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * sixVertexRegularizedBetheLogNormDerivative c epsilon x| <=
      Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let B := 2 - 2 * Real.cos x
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : (a - 1) ^ 2 <= A := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := (sq_pos_of_pos (sub_pos.mpr ha)).trans_le hA
  have hBpos : 0 < B := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [<- Real.cos_abs, <- Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (abs_le.mpr hxIcc)
        (abs_pos.mpr hx)
    linarith
  have hxabs : |x| <= Real.pi := abs_le.mpr hxIcc
  have hsabs : |Real.sin x| <= 1 := Real.abs_sin_le_one x
  have hreg : |x * (-a * Real.sin x / A)| <=
      Real.pi * a / (a - 1) ^ 2 := by
    simp only [abs_mul, abs_div, abs_neg]
    rw [show |a| = a from abs_of_pos (zero_lt_one.trans ha),
      show |A| = A from abs_of_pos hApos]
    rw [show |x| * (a * |Real.sin x| / A) =
      (|x| * a * |Real.sin x|) / A by ring]
    rw [div_le_div_iff₀ hApos (sq_pos_of_pos (sub_pos.mpr ha))]
    have hprod : |x| * |Real.sin x| <= Real.pi := by
      nlinarith [mul_le_mul hxabs hsabs (abs_nonneg (Real.sin x)) Real.pi_pos.le]
    have ha0 : 0 <= a := ha.le.trans' zero_le_one
    calc
      |x| * a * |Real.sin x| * (a - 1) ^ 2 =
          a * (|x| * |Real.sin x|) * (a - 1) ^ 2 := by ring
      _ <= a * Real.pi * (a - 1) ^ 2 := by gcongr
      _ <= a * Real.pi * A := by gcongr
      _ = Real.pi * a * A := by ring
  have hsing0 := abs_mul_sixVertexBetheLogNormDenominatorDerivative_le hx hxIcc
  have hsing : |x * (Real.sin x / (B + epsilon))| <= Real.pi / 2 := by
    have hden : 0 < B + epsilon := add_pos hBpos hepsilon
    rw [abs_mul, abs_div, abs_of_pos hden]
    calc
      |x| * (|Real.sin x| / (B + epsilon)) <=
          |x| * (|Real.sin x| / B) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (abs_nonneg (Real.sin x)) hBpos
            (le_add_of_nonneg_right hepsilon.le)) (abs_nonneg x)
      _ = |x * (Real.sin x / B)| := by
        rw [abs_mul, abs_div, abs_of_pos hBpos]
      _ <= Real.pi / 2 := by simpa [B] using hsing0
  unfold sixVertexRegularizedBetheLogNormDerivative
  dsimp [a, A, B] at hreg hsing ⊢
  calc
    |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x) -
        Real.sin x / (2 - 2 * Real.cos x + epsilon))| <=
        |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x))| +
        |x * (Real.sin x / (2 - 2 * Real.cos x + epsilon))| := by
      rw [mul_sub]
      exact abs_sub _ _
    _ <= Real.pi * a / (a - 1) ^ 2 + Real.pi / 2 :=
      add_le_add hreg hsing
    _ = _ := by dsimp [a]; ring

theorem tendsto_sixVertexRegularizedBetheLogNormDerivative
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
    {iota : Type*} {l : Filter iota} {epsilon : iota -> Real}
    (hepsilon : Tendsto epsilon l (nhds 0)) :
    Tendsto (fun i => sixVertexRegularizedBetheLogNormDerivative c
      (epsilon i) x) l (nhds (sixVertexBetheLogNormDerivative c x)) := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  let B := 2 - 2 * Real.cos x
  have hB : B ≠ 0 := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [<- Real.cos_abs, <- Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (abs_le.mpr hxIcc)
        (abs_pos.mpr hx)
    linarith
  have hden : Tendsto (fun i => B + epsilon i) l (nhds B) :=
    by simpa only [add_zero] using (tendsto_const_nhds.add hepsilon)
  have hnum : Tendsto (fun _ : iota => Real.sin x) l
      (nhds (Real.sin x)) := tendsto_const_nhds
  have hquot : Tendsto (fun i => Real.sin x / (B + epsilon i)) l
      (nhds (Real.sin x / B)) := hnum.div hden hB
  have hfirst : Tendsto (fun _ : iota =>
      -a * Real.sin x / A) l (nhds (-a * Real.sin x / A)) :=
    tendsto_const_nhds
  unfold sixVertexRegularizedBetheLogNormDerivative
    sixVertexBetheLogNormDerivative
  simpa [a, A, B] using hfirst.sub hquot

theorem intervalIntegral_sixVertexBetheLogNormDerivative_mul_offset
    {c : Real} (hc : 2 < c) :
    (∫ x in -Real.pi..Real.pi,
      sixVertexBetheLogNormDerivative c x *
        sixVertexContinuousOffsetFourier c hc x) =
      Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
        sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c) := by
  let epsilon : Nat -> Real := fun k => 1 / (k + 1 : Real)
  let tau := sixVertexContinuousOffsetFourier c hc
  let D : Real := (sixVertexContinuousOffsetFourierLipschitzNNReal c : Real)
  let K : Real := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2
  let C := D * K
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hepsilonPos : ∀ᶠ k : Nat in atTop, 0 < epsilon k :=
    Filter.Eventually.of_forall (fun k => by dsimp [epsilon]; positivity)
  have htauZero : tau 0 = 0 := by
    have h := odd_sixVertexContinuousOffsetFourier hc 0
    change tau (-0) = -tau 0 at h
    rw [neg_zero] at h
    linarith
  have htauLinear (x : Real) : |tau x| <= D * |x| := by
    have h := (lipschitzWith_sixVertexContinuousOffsetFourier hc).dist_le_mul x 0
    change |tau x - tau 0| <= D * |x - 0| at h
    rw [htauZero, sub_zero, sub_zero] at h
    exact h
  have hC : 0 <= C := by
    dsimp [C, D, K]
    have hc2 : 0 < c ^ 2 - 2 := by nlinarith
    have hc1 : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  have hbound (k : Nat) (x : Real)
      (hxI : x ∈ Set.uIoc (-Real.pi) Real.pi) :
      ‖sixVertexRegularizedBetheLogNormDerivative c (epsilon k) x * tau x‖ <= C := by
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x = 0
    · subst x
      rw [htauZero, abs_zero, mul_zero]
      exact hC
    · have hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi := by
        rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
        exact ⟨hxI.1.le, hxI.2⟩
      have hderiv := abs_mul_sixVertexRegularizedBetheLogNormDerivative_le
        hc (by change 0 < 1 / (k + 1 : Real); positivity) hx hxIcc
      have hxpos : 0 < |x| := abs_pos.mpr hx
      have hK : 0 <= K := by
        dsimp [K]
        have hc2 : 0 < c ^ 2 - 2 := by nlinarith
        have hc1 : 0 < c ^ 2 - 1 := by nlinarith
        positivity
      have hratio : |tau x| / |x| <= D :=
        (div_le_iff₀ hxpos).2 (htauLinear x)
      calc
        |sixVertexRegularizedBetheLogNormDerivative c (epsilon k) x| * |tau x| =
            (|x * sixVertexRegularizedBetheLogNormDerivative c (epsilon k) x|) *
              (|tau x| / |x|) := by
          rw [abs_mul]
          field_simp [hxpos.ne']
        _ <= K * D := by
          exact mul_le_mul hderiv hratio (div_nonneg (abs_nonneg _) hxpos.le) hK
        _ = C := by dsimp [C]; ring
  have hIntegral : Tendsto (fun k : Nat =>
      ∫ x in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogNormDerivative c (epsilon k) x * tau x)
      atTop (nhds (∫ x in -Real.pi..Real.pi,
        sixVertexBetheLogNormDerivative c x * tau x)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => C)
    · filter_upwards [hepsilonPos] with k hk
      exact ((continuous_sixVertexRegularizedBetheLogNormDerivative hc hk).mul
        (continuous_sixVertexContinuousOffsetFourier hc)).aestronglyMeasurable
    · filter_upwards [] with k
      filter_upwards [] with x hx
      exact hbound k x hx
    · exact intervalIntegrable_const
    · filter_upwards [] with x hxI
      by_cases hx : x = 0
      · subst x
        simp [sixVertexRegularizedBetheLogNormDerivative,
          sixVertexBetheLogNormDerivative]
      · have hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi := by
          rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
          exact ⟨hxI.1.le, hxI.2⟩
        exact (tendsto_sixVertexRegularizedBetheLogNormDerivative hc hx hxIcc
          hepsilon).mul_const (tau x)
  have hValue : Tendsto (fun k : Nat =>
      ∫ x in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogNormDerivative c (epsilon k) x * tau x)
      atTop (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
        sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c))) := by
    have h := tendsto_sixVertexOffsetLogFourierDampedValue_regularization
      (sixVertexAntiferroelectricLambda_pos hc) hepsilon hepsilonPos
    apply h.congr'
    filter_upwards [hepsilonPos] with k hk
    exact (intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset
      hc hk).symm
  exact tendsto_nhds_unique hIntegral hValue

end

end StatMech.FrontierD
