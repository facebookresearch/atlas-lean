/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierKernelClosedForm





namespace StatMech.FrontierD

noncomputable section

theorem sixVertexXiFourier_pos
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    0 < sixVertexXiFourier lam alpha := by
  rw [sixVertexXiFourier_eq hlam]
  exact div_pos (Real.sinh_pos_iff.mpr hlam)
    (by
      have hcosh : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
      linarith [Real.cos_le_one alpha])

theorem sixVertexXiFourier_neg (lam alpha : Real) :
    sixVertexXiFourier lam (-alpha) = sixVertexXiFourier lam alpha := by
  unfold sixVertexXiFourier sixVertexXiFourierTerm
  congr 1
  apply tsum_congr
  intro n
  rw [mul_neg, Real.cos_neg]

private def sixVertexXiFourierTermContinuous
    (lam : Real) (n : Nat) : C(Real, Real) :=
  ⟨sixVertexXiFourierTerm lam n, by
    unfold sixVertexXiFourierTerm
    fun_prop⟩

theorem intervalIntegral_zero_pi_sixVertexXiFourierTerm
    (lam : Real) (n : Nat) :
    (∫ alpha in (0 : Real)..Real.pi,
      sixVertexXiFourierTerm lam n alpha) = 0 := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hscaled := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : Real)) (b := Real.pi) (f := Real.cos) m
  have hrhs : (∫ x in (0 : Real)..m * Real.pi, Real.cos x) = 0 := by
    rw [integral_cos]
    have hpos : Real.sin (m * Real.pi) = 0 := by
      dsimp [m]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.sin_nat_mul_pi (n + 1)
    rw [hpos, Real.sin_zero, sub_zero]
  simp only [mul_zero] at hscaled
  rw [hrhs] at hscaled
  have hcoszero :
      (∫ alpha in (0 : Real)..Real.pi, Real.cos (m * alpha)) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hm
  unfold sixVertexXiFourierTerm
  change (∫ alpha in (0 : Real)..Real.pi,
    (2 * Real.exp (-(m * lam))) * Real.cos (m * alpha)) = 0
  rw [intervalIntegral.integral_const_mul, hcoszero, mul_zero]

theorem intervalIntegral_zero_pi_sixVertexXiFourier
    {lam : Real} (hlam : 0 < lam) :
    (∫ alpha in (0 : Real)..Real.pi,
      sixVertexXiFourier lam alpha) = Real.pi := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (0 : Real) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun n : Nat =>
      ‖(sixVertexXiFourierTermContinuous lam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam n)]
    intro alpha
    exact norm_sixVertexXiFourierTerm_le lam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ alpha in (0 : Real)..Real.pi,
        sixVertexXiFourierTerm lam n alpha) =
      ∫ alpha in (0 : Real)..Real.pi,
        ∑' n : Nat, sixVertexXiFourierTerm lam n alpha := by
    simpa only [sixVertexXiFourierTermContinuous] using hswap
  have hseries :
      (∫ alpha in (0 : Real)..Real.pi,
        ∑' n : Nat, sixVertexXiFourierTerm lam n alpha) = 0 := by
    rw [<- hswap']
    rw [show (fun n : Nat => ∫ alpha in (0 : Real)..Real.pi,
        sixVertexXiFourierTerm lam n alpha) =
      (fun _ : Nat => 0) by
        funext n
        exact intervalIntegral_zero_pi_sixVertexXiFourierTerm lam n,
      tsum_zero]
  have hseriesInt : IntervalIntegrable
      (fun alpha => ∑' n : Nat, sixVertexXiFourierTerm lam n alpha)
      MeasureTheory.volume 0 Real.pi := by
    have hcont : Continuous
        (fun alpha => ∑' n : Nat, sixVertexXiFourierTerm lam n alpha) := by
      apply continuous_tsum
      · intro n
        unfold sixVertexXiFourierTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant hlam
      · intro n alpha
        exact norm_sixVertexXiFourierTerm_le lam n alpha
    exact hcont.intervalIntegrable _ _
  simp_rw [sixVertexXiFourier]
  rw [intervalIntegral.integral_add intervalIntegrable_const hseriesInt,
    intervalIntegral.integral_const, hseries]
  simp


def sixVertexRapidityMomentum (lam alpha : Real) : Real :=
  ∫ t in (0 : Real)..alpha, sixVertexXiFourier lam t

theorem hasDerivAt_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexRapidityMomentum lam)
      (sixVertexXiFourier lam alpha) alpha := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_sixVertexXiFourier hlam).intervalIntegrable _ _
  · exact (continuous_sixVertexXiFourier hlam).stronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_sixVertexXiFourier hlam).continuousAt

theorem strictMono_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) :
    StrictMono (sixVertexRapidityMomentum lam) :=
  strictMono_of_hasDerivAt_pos
    (hasDerivAt_sixVertexRapidityMomentum hlam)
    (sixVertexXiFourier_pos hlam)

theorem sixVertexRapidityMomentum_pi
    {lam : Real} (hlam : 0 < lam) :
    sixVertexRapidityMomentum lam Real.pi = Real.pi :=
  intervalIntegral_zero_pi_sixVertexXiFourier hlam

theorem sixVertexRapidityMomentum_neg_pi
    {lam : Real} (hlam : 0 < lam) :
    sixVertexRapidityMomentum lam (-Real.pi) = -Real.pi := by
  have hleft :
      (∫ t in -Real.pi..(0 : Real), sixVertexXiFourier lam t) = Real.pi := by
    have hnegIntegral := intervalIntegral.integral_comp_neg
      (f := sixVertexXiFourier lam) (a := 0) (b := Real.pi)
    have hnegIntegral' :
        (∫ t in (0 : Real)..Real.pi, sixVertexXiFourier lam (-t)) =
          ∫ t in -Real.pi..(0 : Real), sixVertexXiFourier lam t := by
      simpa only [neg_zero] using hnegIntegral
    rw [<- hnegIntegral']
    apply (intervalIntegral.integral_congr fun t _ => ?_).trans
      (intervalIntegral_zero_pi_sixVertexXiFourier hlam)
    exact sixVertexXiFourier_neg lam t
  rw [sixVertexRapidityMomentum, intervalIntegral.integral_symm, hleft]

theorem sixVertexRapidityMomentum_mem_Icc
    {lam : Real} (hlam : 0 < lam) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRapidityMomentum lam alpha ∈ Set.Icc (-Real.pi) Real.pi := by
  have hmono := (strictMono_sixVertexRapidityMomentum hlam).monotone
  constructor
  · rw [<- sixVertexRapidityMomentum_neg_pi hlam]
    exact hmono halpha.1
  · rw [<- sixVertexRapidityMomentum_pi hlam]
    exact hmono halpha.2

end

end StatMech.FrontierD
