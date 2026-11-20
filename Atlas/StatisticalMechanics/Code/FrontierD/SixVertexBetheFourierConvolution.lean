/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierOrthogonality





namespace StatMech.FrontierD

noncomputable section



def sixVertexXiFourierTerm (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-((n + 1 : Real) * lam)) *
    Real.cos ((n + 1 : Real) * alpha)


def sixVertexXiFourier (lam alpha : Real) : Real :=
  1 + ∑' n : Nat, sixVertexXiFourierTerm lam n alpha

theorem norm_sixVertexXiFourierTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexXiFourierTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant lam n := by
  rw [sixVertexXiFourierTerm, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 <= (2 : Real)),
    abs_of_pos (Real.exp_pos _)]
  have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc
    2 * Real.exp (-((n + 1 : Real) * lam)) *
        |Real.cos ((n + 1 : Real) * alpha)|
      <= 2 * Real.exp (-((n + 1 : Real) * lam)) * 1 := by gcongr
    _ = sixVertexFourierRootDensityMajorant lam n := by
      rw [sixVertexFourierRootDensityMajorant, mul_one, <- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexXiFourierTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexXiFourierTerm lam n alpha) :=
  (summable_sixVertexFourierRootDensityMajorant hlam).of_norm_bounded
    (fun n => norm_sixVertexXiFourierTerm_le lam n alpha)

theorem continuous_sixVertexXiFourier
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexXiFourier lam) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexXiFourierTerm
    fun_prop
  · exact summable_sixVertexFourierRootDensityMajorant hlam
  · intro n alpha
    exact norm_sixVertexXiFourierTerm_le lam n alpha

theorem intervalIntegral_cos_succ_mul_sub (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta))) = 0 := by
  let m : Nat := n + 1
  let z : Int := m
  have hm : 0 < m := by dsimp [m]; omega
  have hz : z ≠ 0 := by dsimp [z]; exact_mod_cast hm.ne'
  have hcosInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun beta => Real.sin ((m : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hid (beta : Real) :
      Real.cos ((m : Real) * (alpha - beta)) =
        Real.cos ((m : Real) * alpha) * Real.cos ((m : Real) * beta) +
          Real.sin ((m : Real) * alpha) * Real.sin ((m : Real) * beta) := by
    rw [mul_sub, Real.cos_sub]
  suffices (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * (alpha - beta))) = 0 by
    simpa only [m, Nat.cast_add, Nat.cast_one] using this
  rw [intervalIntegral.integral_congr (fun beta _ => hid beta)]
  rw [intervalIntegral.integral_add
    (hcosInt.const_mul _) (hsinInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hcast (beta : Real) : (z : Real) * beta = (m : Real) * beta := by
    dsimp [z]
    norm_cast
  have hcosZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((m : Real) * beta)) = 0 := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          Real.cos ((z : Real) * beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact congrArg Real.cos (hcast beta).symm
      _ = 0 := by rw [intervalIntegral_cos_int_mul z, if_neg hz]
  have hsinZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.sin ((m : Real) * beta)) = 0 := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          Real.sin ((z : Real) * beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact congrArg Real.sin (hcast beta).symm
      _ = 0 := intervalIntegral_sin_int_mul z
  rw [hcosZero, hsinZero]
  ring

theorem intervalIntegral_shiftedCos_mul_fourierRootDensityTerm
    (lam : Real) (n j : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensityTerm lam j beta) =
      if n = j then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) /
          Real.cosh ((n + 1 : Real) * lam)
      else 0 := by
  unfold sixVertexFourierRootDensityTerm
  simp_rw [show ∀ beta : Real,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (Real.cos ((j + 1 : Real) * beta) /
            Real.cosh ((j + 1 : Real) * lam)) =
        (Real.cos ((n + 1 : Real) * (alpha - beta)) *
          Real.cos ((j + 1 : Real) * beta)) *
            (1 / Real.cosh ((j + 1 : Real) * lam)) by
      intro beta
      ring]
  rw [intervalIntegral.integral_mul_const,
    show (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        Real.cos ((j + 1 : Real) * beta)) =
      if n + 1 = j + 1 then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) else 0 by
      simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul
          (m := n + 1) (n := j + 1) (by omega) (by omega) alpha]
  by_cases hnj : n = j
  · subst j
    simp
    ring
  · simp [hnj]

private def shiftedCosMulFourierRootDensityTermContinuous
    (lam : Real) (n j : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
      sixVertexFourierRootDensityTerm lam j beta, by
    unfold sixVertexFourierRootDensityTerm
    fun_prop⟩



theorem intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) =
      Real.pi * Real.cos ((n + 1 : Real) * alpha) /
        Real.cosh ((n + 1 : Real) * lam) := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun j : Nat =>
      ‖(shiftedCosMulFourierRootDensityTermContinuous lam n j alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam j)]
    intro beta
    change |Real.cos ((n + 1 : Real) * (alpha - (beta : Real))) *
      sixVertexFourierRootDensityTerm lam j beta| <=
        sixVertexFourierRootDensityMajorant lam j
    rw [abs_mul]
    calc
      |Real.cos ((n + 1 : Real) * (alpha - beta))| *
          |sixVertexFourierRootDensityTerm lam j beta|
        <= 1 * sixVertexFourierRootDensityMajorant lam j := by
          apply mul_le_mul
          · exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
          · simpa only [Real.norm_eq_abs] using
              norm_sixVertexFourierRootDensityTerm_le hlam j (beta : Real)
          · exact abs_nonneg _
          · norm_num
      _ = sixVertexFourierRootDensityMajorant lam j := one_mul _
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' j : Nat, ∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' j : Nat, Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta) := by
    simpa only [shiftedCosMulFourierRootDensityTermContinuous] using hswap
  have hseries :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) =
      ∑' j : Nat, ∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          (∑' j : Nat, Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexFourierRootDensityTerm lam j beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact tsum_mul_left.symm
      _ = _ := hswap'.symm
  have hconstInt : IntervalIntegrable
      (fun beta => (1 / 2 : Real) *
        Real.cos ((n + 1 : Real) * (alpha - beta))) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hseriesInt : IntervalIntegrable
      (fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
        (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    have hcont : Continuous
        (fun beta => ∑' j : Nat,
          sixVertexFourierRootDensityTerm lam j beta) := by
      apply continuous_tsum
      · intro j
        unfold sixVertexFourierRootDensityTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant hlam
      · intro j beta
        exact norm_sixVertexFourierRootDensityTerm_le hlam j beta
    exact ((by fun_prop : Continuous (fun beta =>
      Real.cos ((n + 1 : Real) * (alpha - beta)))).mul hcont).intervalIntegrable _ _
  simp_rw [sixVertexFourierRootDensity]
  rw [show (fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
      (1 / 2 + ∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) =
      (fun beta => (1 / 2 : Real) *
          Real.cos ((n + 1 : Real) * (alpha - beta)) +
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) by
      funext beta
      ring]
  rw [intervalIntegral.integral_add hconstInt hseriesInt,
    intervalIntegral.integral_const_mul,
    intervalIntegral_cos_succ_mul_sub, mul_zero, hseries]
  rw [show (fun j : Nat => ∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensityTerm lam j beta) =
      (fun j : Nat => if n = j then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) /
          Real.cosh ((n + 1 : Real) * lam) else 0) by
      funext j
      exact intervalIntegral_shiftedCos_mul_fourierRootDensityTerm
        lam n j alpha]
  rw [zero_add]
  simpa only [eq_comm] using
    (tsum_ite_eq n (fun _ : Nat =>
      Real.pi * Real.cos ((n + 1 : Real) * alpha) /
        Real.cosh ((n + 1 : Real) * lam)))


def sixVertexFourierRootDensityNormBound (lam : Real) : Real :=
  1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n

theorem sixVertexFourierRootDensityNormBound_nonneg
    (lam : Real) :
    0 <= sixVertexFourierRootDensityNormBound lam := by
  unfold sixVertexFourierRootDensityNormBound
  have hsum : 0 <= ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n :=
    tsum_nonneg fun n => by
      unfold sixVertexFourierRootDensityMajorant
      positivity
  linarith

theorem norm_sixVertexFourierRootDensity_le
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    ‖sixVertexFourierRootDensity lam alpha‖ <=
      sixVertexFourierRootDensityNormBound lam := by
  have hmajor := summable_sixVertexFourierRootDensityMajorant hlam
  have hnorm : Summable (fun n : Nat =>
      ‖sixVertexFourierRootDensityTerm lam n alpha‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha) hmajor
  rw [sixVertexFourierRootDensity, sixVertexFourierRootDensityNormBound]
  calc
    ‖1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha‖
      <= ‖(1 / 2 : Real)‖ +
          ‖∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha‖ :=
        norm_add_le _ _
    _ <= 1 / 2 + ∑' n : Nat,
        ‖sixVertexFourierRootDensityTerm lam n alpha‖ := by
      rw [Real.norm_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
      gcongr
      exact norm_tsum_le_tsum_norm hnorm
    _ <= 1 / 2 + ∑' n : Nat,
        sixVertexFourierRootDensityMajorant lam n := by
      have h := hnorm.tsum_le_tsum
        (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha) hmajor
      linarith



def sixVertexXiRootConvolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-2 * ((n + 1 : Real) * lam)) * Real.pi *
    Real.cos ((n + 1 : Real) * alpha) /
      Real.cosh ((n + 1 : Real) * lam)

theorem intervalIntegral_XiFourierTerm_mul_rootDensity
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
        sixVertexFourierRootDensity lam beta) =
      sixVertexXiRootConvolutionTerm lam n alpha := by
  unfold sixVertexXiFourierTerm sixVertexXiRootConvolutionTerm
  simp_rw [show ∀ beta : Real,
      (2 * Real.exp (-((n + 1 : Real) * (2 * lam))) *
          Real.cos ((n + 1 : Real) * (alpha - beta))) *
          sixVertexFourierRootDensity lam beta =
        (2 * Real.exp (-((n + 1 : Real) * (2 * lam)))) *
          (Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexFourierRootDensity lam beta) by
      intro beta
      ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity hlam]
  ring

private def XiFourierTermMulRootDensityContinuous
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
      sixVertexFourierRootDensity lam beta, by
    exact (by
      unfold sixVertexXiFourierTerm
      fun_prop : Continuous _).mul (continuous_sixVertexFourierRootDensity hlam)⟩


theorem intervalIntegral_XiFourier_mul_rootDensity
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourier (2 * lam) (alpha - beta) *
        sixVertexFourierRootDensity lam beta) =
      Real.pi + ∑' n : Nat, sixVertexXiRootConvolutionTerm lam n alpha := by
  have h2lam : 0 < 2 * lam := mul_pos (by norm_num) hlam
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hmajorMul : Summable (fun n : Nat =>
      sixVertexFourierRootDensityMajorant (2 * lam) n *
        sixVertexFourierRootDensityNormBound lam) := by
    simpa [mul_comm] using Summable.mul_left
      (sixVertexFourierRootDensityNormBound lam)
      (summable_sixVertexFourierRootDensityMajorant h2lam)
  have hnorm : Summable (fun n : Nat =>
      ‖(XiFourierTermMulRootDensityContinuous hlam n alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajorMul
    rw [ContinuousMap.norm_le _
      (mul_nonneg
        (by
          unfold sixVertexFourierRootDensityMajorant
          positivity)
        (sixVertexFourierRootDensityNormBound_nonneg lam))]
    intro beta
    change |sixVertexXiFourierTerm (2 * lam) n (alpha - (beta : Real)) *
      sixVertexFourierRootDensity lam beta| <= _
    rw [abs_mul]
    apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - (beta : Real))
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexFourierRootDensity_le hlam (beta : Real)
    · exact abs_nonneg _
    · unfold sixVertexFourierRootDensityMajorant
      positivity
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta) := by
    simpa only [XiFourierTermMulRootDensityContinuous] using hswap
  have hrootInt : IntervalIntegrable
      (sixVertexFourierRootDensity lam) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (continuous_sixVertexFourierRootDensity hlam).intervalIntegrable _ _
  have hseriesContinuous : Continuous
      (fun beta => ∑' n : Nat,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexXiFourierTerm
      fun_prop
    · exact summable_sixVertexFourierRootDensityMajorant h2lam
    · intro n beta
      exact norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - beta)
  have hseriesInt : IntervalIntegrable
      (fun beta => (∑' n : Nat,
          sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (hseriesContinuous.mul (continuous_sixVertexFourierRootDensity hlam))
      |>.intervalIntegrable _ _
  simp_rw [sixVertexXiFourier]
  rw [show (fun beta =>
      (1 + ∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) =
      (fun beta => sixVertexFourierRootDensity lam beta +
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexFourierRootDensity lam beta) by
      funext beta
      ring]
  rw [intervalIntegral.integral_add hrootInt hseriesInt,
    intervalIntegral_sixVertexFourierRootDensity hlam]
  have hseriesSwap :
      (∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexFourierRootDensity lam beta) =
      ∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
            sixVertexFourierRootDensity lam beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact tsum_mul_right.symm
      _ = _ := hswap'.symm
  rw [hseriesSwap]
  congr 1
  apply tsum_congr
  intro n
  exact intervalIntegral_XiFourierTerm_mul_rootDensity hlam n alpha

theorem norm_sixVertexXiRootConvolutionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexXiRootConvolutionTerm lam n alpha‖ <=
      Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n := by
  have hpi : 0 <= Real.pi := Real.pi_pos.le
  have hmajor : 0 <= sixVertexFourierRootDensityMajorant (2 * lam) n := by
    unfold sixVertexFourierRootDensityMajorant
    positivity
  have hcosh : 1 <= Real.cosh ((n + 1 : Real) * lam) := Real.one_le_cosh _
  have hcoshPos : 0 < Real.cosh ((n + 1 : Real) * lam) := Real.cosh_pos _
  have hxi := norm_sixVertexXiFourierTerm_le (2 * lam) n alpha
  have hrepr : sixVertexXiRootConvolutionTerm lam n alpha =
      Real.pi * sixVertexXiFourierTerm (2 * lam) n alpha /
        Real.cosh ((n + 1 : Real) * lam) := by
    unfold sixVertexXiRootConvolutionTerm sixVertexXiFourierTerm
    ring
  rw [hrepr, norm_div, norm_mul, Real.norm_of_nonneg hpi,
    Real.norm_of_nonneg hcoshPos.le]
  calc
    Real.pi * ‖sixVertexXiFourierTerm (2 * lam) n alpha‖ /
        Real.cosh ((n + 1 : Real) * lam)
      <= Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n /
          Real.cosh ((n + 1 : Real) * lam) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxi hpi) hcoshPos.le
    _ <= Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n := by
      rw [div_le_iff₀ hcoshPos]
      nlinarith [mul_le_mul_of_nonneg_left hcosh hmajor]

theorem summable_sixVertexXiRootConvolutionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n : Nat => sixVertexXiRootConvolutionTerm lam n alpha) := by
  have h2lam : 0 < 2 * lam := mul_pos (by norm_num) hlam
  have hmajor : Summable (fun n : Nat =>
      Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n) :=
    Summable.mul_left Real.pi
      (summable_sixVertexFourierRootDensityMajorant h2lam)
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexXiRootConvolutionTerm_le lam n alpha)



theorem sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexXiFourierTerm lam n alpha -
        (1 / (2 * Real.pi)) * sixVertexXiRootConvolutionTerm lam n alpha =
      sixVertexFourierRootDensityTerm lam n alpha := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := by
    rw [<- Real.exp_neg]
  have hnegTwo : Real.exp (-2 * x) =
      Real.exp (-x) * Real.exp (-x) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  have hexpProd : Real.exp x * Real.exp (-x) = 1 := by
    rw [<- Real.exp_add]
    simp
  unfold sixVertexXiFourierTerm sixVertexXiRootConvolutionTerm
    sixVertexFourierRootDensityTerm
  change 2 * Real.exp (-x) * Real.cos (m * alpha) -
      (1 / (2 * Real.pi)) *
        (2 * Real.exp (-2 * x) * Real.pi * Real.cos (m * alpha) /
          Real.cosh x) =
    Real.cos (m * alpha) / Real.cosh x
  rw [hnegTwo, hneg, Real.cosh_eq]
  field_simp [hexp, hpi]
  calc
    Real.cos (m * alpha) *
        (Real.exp x * (Real.exp x + Real.exp (-x)) - 1) =
      Real.exp x ^ 2 * Real.cos (m * alpha) +
        Real.cos (m * alpha) *
          (Real.exp x * Real.exp (-x) - 1) := by ring
    _ = Real.exp x ^ 2 * Real.cos (m * alpha) := by
      rw [hexpProd]
      ring



theorem sixVertexFourierRootDensity_integralEquation
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexFourierRootDensity lam alpha =
      sixVertexXiFourier lam alpha -
        (1 / (2 * Real.pi)) *
          ∫ beta in -Real.pi..Real.pi,
            sixVertexXiFourier (2 * lam) (alpha - beta) *
              sixVertexFourierRootDensity lam beta := by
  let q : Real := 1 / (2 * Real.pi)
  have hXi : Summable (fun n : Nat => sixVertexXiFourierTerm lam n alpha) :=
    summable_sixVertexXiFourierTerm hlam alpha
  have hConv : Summable (fun n : Nat =>
      sixVertexXiRootConvolutionTerm lam n alpha) :=
    summable_sixVertexXiRootConvolutionTerm hlam alpha
  have hRoot : Summable (fun n : Nat =>
      sixVertexFourierRootDensityTerm lam n alpha) :=
    summable_sixVertexFourierRootDensityTerm hlam alpha
  have hqConv : Summable (fun n : Nat =>
      q * sixVertexXiRootConvolutionTerm lam n alpha) :=
    Summable.mul_left q hConv
  have hseries :
      (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha) =
        (∑' n : Nat, sixVertexXiFourierTerm lam n alpha) -
          q * ∑' n : Nat, sixVertexXiRootConvolutionTerm lam n alpha := by
    have hpoint : (fun n : Nat =>
        sixVertexFourierRootDensityTerm lam n alpha) =
      (fun n : Nat => sixVertexXiFourierTerm lam n alpha -
        q * sixVertexXiRootConvolutionTerm lam n alpha) := by
      funext n
      exact (sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm
        lam n alpha).symm
    rw [hpoint]
    have hsum := hXi.hasSum.sub hqConv.hasSum
    rw [hsum.tsum_eq, tsum_mul_left]
  rw [intervalIntegral_XiFourier_mul_rootDensity hlam alpha]
  unfold sixVertexFourierRootDensity sixVertexXiFourier
  dsimp [q] at hseries ⊢
  rw [hseries]
  field_simp [Real.pi_ne_zero]
  ring

end

end StatMech.FrontierD
