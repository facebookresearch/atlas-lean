/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Code.FrontierA.EntireExponentialLogAffine










open Filter Metric Real Set Topology
open ValueDistribution

namespace StatMech.FrontierA

noncomputable section



theorem re_apply_le_three_mul_proximity_exp
    (g : Complex → Complex) (hg : Differentiable Complex g)
    {R : Real} (hR : 0 < R) {w : Complex} (hw : ‖w‖ ≤ R / 2) :
    (g w).re ≤ 3 * proximity (fun z ↦ Complex.exp (g z)) ⊤ R := by
  let u : Complex → Real := fun z ↦ (g z).re
  have hu : InnerProductSpace.HarmonicOnNhd u (closedBall 0 R) := by
    intro z hz
    exact (hg.analyticAt z).harmonicAt_re
  have hwBall : w ∈ ball (0 : Complex) R := by
    rw [mem_ball, dist_zero_right]
    linarith [norm_nonneg w]
  let K : Complex → Real := fun z ↦
    ((z + w) / (z - w)).re
  have hpoisson : circleAverage (fun z ↦ K z * u z) 0 R = u w := by
    have h := hu.circleAverage_re_herglotzRieszKernel_smul hwBall
    simpa [K, u, herglotzRieszKernel_fun_def] using h
  have hdenom (z : Complex) (hz : z ∈ sphere (0 : Complex) R) :
      z - w ≠ 0 := by
    intro hzw
    have hzw' : z = w := sub_eq_zero.mp hzw
    have hzNorm : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos hR] using hz
    rw [hzw'] at hzNorm
    linarith
  have hquotContinuous : ContinuousOn (fun z : Complex ↦ (z + w) / (z - w))
      (sphere (0 : Complex) R) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hdenom
  have hKContinuous : ContinuousOn K (sphere (0 : Complex) R) := by
    exact Complex.continuous_re.comp_continuousOn hquotContinuous
  have huContinuous : ContinuousOn u (sphere (0 : Complex) R) := by
    exact Complex.continuous_re.comp_continuousOn hg.continuous.continuousOn
  have hleft : CircleIntegrable (fun z ↦ K z * u z) 0 R := by
    have hc : ContinuousOn (fun z ↦ K z * u z)
        (sphere (0 : Complex) |R|) := by
      simpa [abs_of_pos hR] using hKContinuous.mul huContinuous
    exact hc.circleIntegrable'
  have hright : CircleIntegrable
      (fun z ↦ (3 : Real) • max (u z) 0) 0 R := by
    apply ContinuousOn.circleIntegrable'
    have humax : Continuous (fun z ↦ max (u z) 0) :=
      (Complex.continuous_re.comp hg.continuous).max continuous_const
    exact humax.continuousOn.const_smul 3
  have hpoint (z : Complex) (hz : z ∈ sphere (0 : Complex) |R|) :
      K z * u z ≤ (3 : Real) • max (u z) 0 := by
    have hz' : z ∈ sphere (0 : Complex) R := by
      simpa [abs_of_pos hR] using hz
    have hKupper0 := re_herglotzRieszKernel_le hz' hwBall
    have hKlower0 := le_re_herglotzRieszKernel hz' hwBall
    have hwNorm : ‖w‖ ≤ R / 2 := hw
    have hdenPos : 0 < R - ‖w‖ := by linarith [norm_nonneg w]
    have hsumPos : 0 < R + ‖w‖ := by positivity
    have hKupper : K z ≤ 3 := by
      dsimp [K]
      calc
        ((z + w) / (z - w)).re ≤
            (R + ‖w‖) / (R - ‖w‖) := by
              simpa using hKupper0
        _ ≤ 3 := by
          rw [div_le_iff₀ hdenPos]
          linarith
    have hKnonneg : 0 ≤ K z := by
      have hratio : 0 ≤ (R - ‖w‖) / (R + ‖w‖) :=
        div_nonneg (by linarith) hsumPos.le
      exact hratio.trans (by simpa [K] using hKlower0)
    simp only [smul_eq_mul]
    by_cases huz : 0 ≤ u z
    · rw [max_eq_left huz]
      exact mul_le_mul_of_nonneg_right hKupper huz
    · rw [max_eq_right (le_of_not_ge huz)]
      simpa using mul_nonpos_of_nonneg_of_nonpos hKnonneg (le_of_not_ge huz)
  have havg := circleAverage_mono hleft hright hpoint
  rw [hpoisson] at havg
  change u w ≤ 3 * proximity (fun z ↦ Complex.exp (g z)) ⊤ R
  rw [proximity_top]
  have hlog : (fun z ↦ max (u z) 0) =
      (fun z ↦ log⁺ ‖Complex.exp (g z)‖) := by
    funext z
    rw [Complex.norm_exp]
    simp [u, posLog, max_comm]
  rw [← hlog]
  rw [Real.circleAverage_fun_smul] at havg
  simpa only [smul_eq_mul] using havg



theorem exists_affine_of_entire_exp_proximity_growth
    (g : Complex → Complex) (hg : Differentiable Complex g)
    (C D : Real) (hD : 0 ≤ D)
    (hgrowth : ∀ R : Real, 1 ≤ R →
      proximity (fun z ↦ Complex.exp (g z)) ⊤ R ≤ C + D * R) :
    ∃ a b : Complex, ∀ z, g z = a * z + b := by
  let A : Real := Real.exp (3 * C + 6 * D)
  let B : Real := 6 * D
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply exists_affine_of_entire_exp_growth g hg A B hA hB
  intro z
  let R : Real := 2 * ‖z‖ + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRone : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hzhalf : ‖z‖ ≤ R / 2 := by dsimp [R]; linarith
  have hre := re_apply_le_three_mul_proximity_exp g hg hR hzhalf
  have hprox := hgrowth R hRone
  have hre' : (g z).re ≤ 3 * C + 6 * D + B * ‖z‖ := by
    calc
      (g z).re ≤
          3 * proximity (fun w ↦ Complex.exp (g w)) ⊤ R := hre
      _ ≤ 3 * (C + D * R) := by gcongr
      _ = 3 * C + 6 * D + B * ‖z‖ := by
        dsimp [R, B]
        ring
  rw [Complex.norm_exp]
  change Real.exp (g z).re ≤ A * Real.exp (B * ‖z‖)
  rw [show A = Real.exp (3 * C + 6 * D) by rfl, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hre'



theorem proximity_top_le_of_exp_growth
    (f : Complex → Complex) (hf : Differentiable Complex f)
    (A B R : Real) (_hA : 0 < A) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) :
    proximity f ⊤ R ≤ log⁺ A + B * R := by
  rw [proximity_top]
  apply circleAverage_mono_on_of_le_circle
  · have hfAnalytic : AnalyticOnNhd Complex f univ :=
      fun z _ ↦ hf.analyticAt z
    exact (hfAnalytic.mono (by simp)).meromorphicOn.circleIntegrable_posLog_norm
  · intro z hz
    have hzNorm : ‖z‖ = R := by
      have hR0 : 0 ≤ R := (zero_le_one.trans hR)
      simpa [mem_sphere, dist_zero_right, abs_of_nonneg hR0] using hz
    have hnonneg : 0 ≤ ‖f z‖ := norm_nonneg _
    have hmono := Real.posLog_le_posLog hnonneg (hgrowth z)
    calc
      log⁺ ‖f z‖ ≤ log⁺ (A * Real.exp (B * ‖z‖)) := hmono
      _ ≤ log⁺ A + log⁺ (Real.exp (B * ‖z‖)) := Real.posLog_mul
      _ = log⁺ A + B * R := by
        rw [hzNorm]
        have hBR : 0 ≤ B * R := mul_nonneg hB (zero_le_one.trans hR)
        simp [posLog, Real.log_exp, hBR]




theorem exists_affine_of_matched_entire_exp_growth
    (f p g : Complex → Complex)
    (hf : Differentiable Complex f) (hp : Differentiable Complex p)
    (hg : Differentiable Complex g) (hp0 : p 0 ≠ 0)
    (hfactor : ∀ z, f z = p z * Complex.exp (g z))
    (Af Bf Ap Bp : Real)
    (hAf : 0 < Af) (hBf : 0 ≤ Bf)
    (hAp : 0 < Ap) (hBp : 0 ≤ Bp)
    (hfGrowth : ∀ z, ‖f z‖ ≤ Af * Real.exp (Bf * ‖z‖))
    (hpGrowth : ∀ z, ‖p z‖ ≤ Ap * Real.exp (Bp * ‖z‖)) :
    ∃ a b : Complex, ∀ z, g z = a * z + b := by
  have hfAnalytic : AnalyticOnNhd Complex f univ :=
    fun z _ ↦ hf.analyticAt z
  have hpAnalytic : AnalyticOnNhd Complex p univ :=
    fun z _ ↦ hp.analyticAt z
  have hfMero : Meromorphic f := meromorphicOn_univ.mp hfAnalytic.meromorphicOn
  have hpMero : Meromorphic p := meromorphicOn_univ.mp hpAnalytic.meromorphicOn
  have hpPoleCount : logCounting p ⊤ = 0 := by
    rw [logCounting_top,
      negPart_eq_zero.mpr
        (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hpAnalytic)]
    simp
  let K : Real := max |Real.log ‖p 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt p 0‖|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hquotient :
      (fun z ↦ Complex.exp (g z)) =ᶠ[codiscrete Complex] f * p⁻¹ := by
    have hpNe := hpAnalytic.preimage_zero_mem_codiscrete hp0
    filter_upwards [hpNe] with z hz
    have hpz : p z ≠ 0 := by simpa using hz
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [hfactor z]
    field_simp
  have hinvProximity (R : Real) (hR : 1 ≤ R) :
      proximity p⁻¹ ⊤ R ≤ proximity p ⊤ R + K := by
    have hfirst := characteristic_sub_characteristic_inv_le hpMero (R := R)
    have hcharInv : characteristic p⁻¹ ⊤ R ≤
        characteristic p ⊤ R + K := by
      have hneg : characteristic p⁻¹ ⊤ R - characteristic p ⊤ R ≤
          |characteristic p ⊤ R - characteristic p⁻¹ ⊤ R| := by
        simpa [abs_sub_comm] using
          (le_abs_self (characteristic p⁻¹ ⊤ R - characteristic p ⊤ R))
      dsimp [K]
      linarith
    have hcountInv : 0 ≤ logCounting p⁻¹ ⊤ R :=
      logCounting_nonneg hR
    rw [characteristic, Pi.add_apply] at hcharInv
    change proximity p⁻¹ ⊤ R + logCounting p⁻¹ ⊤ R ≤
      (proximity p ⊤ R + logCounting p ⊤ R) + K at hcharInv
    rw [congrFun hpPoleCount R] at hcharInv
    simp only [Pi.zero_apply, add_zero] at hcharInv
    linarith
  apply exists_affine_of_entire_exp_proximity_growth g hg
    (log⁺ Af + log⁺ Ap + K) (Bf + Bp) (add_nonneg hBf hBp)
  intro R hR
  have hRne : R ≠ 0 := by linarith
  have hcongr := proximity_congr_codiscrete hquotient hRne (
    a := (⊤ : WithTop Complex))
  have hmul := proximity_mul_top_le hfMero hpMero.inv
  have hfProx := proximity_top_le_of_exp_growth
    f hf Af Bf R hAf hBf hR hfGrowth
  have hpProx := proximity_top_le_of_exp_growth
    p hp Ap Bp R hAp hBp hR hpGrowth
  calc
    proximity (fun z ↦ Complex.exp (g z)) ⊤ R =
        proximity (f * p⁻¹) ⊤ R := hcongr
    _ ≤ proximity f ⊤ R + proximity p⁻¹ ⊤ R := hmul R
    _ ≤ proximity f ⊤ R + (proximity p ⊤ R + K) := by
      gcongr
      exact hinvProximity R hR
    _ ≤ (log⁺ Af + Bf * R) + ((log⁺ Ap + Bp * R) + K) := by
      gcongr
    _ = (log⁺ Af + log⁺ Ap + K) + (Bf + Bp) * R := by ring

end

end StatMech.FrontierA
