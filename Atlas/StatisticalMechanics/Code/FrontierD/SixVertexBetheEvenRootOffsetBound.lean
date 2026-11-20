/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootGapFirstOrder
import Code.FrontierD.SixVertexBetheOffsetFinite





namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeDensityInvWidthConstant
    (c : Real) (r : Nat) : Real :=
  sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r
      (sixVertexTailFiniteDensityFloor c) /
    (1 - sixVertexRootDensityContractionRate c)

theorem sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    0 <= sixVertexFixedChargeDensityInvWidthConstant c r := by
  have hfloor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
  have hK := sixVertexRootDensityKernelUniformBound_nonneg hc
  have hscale := sixVertexRootDensityScale_pos hc
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hfinite : 0 <= sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    positivity
  unfold sixVertexFixedChargeDensityInvWidthConstant
  apply div_nonneg
  · unfold sixVertexFixedChargeDensityStabilityErrorOfLower
    apply add_nonneg
    · apply add_nonneg
      · apply mul_nonneg hrate.1
        positivity
      · exact mul_nonneg (by positivity) hK
    · unfold sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      apply div_nonneg
      · apply add_nonneg
        · positivity
        · exact mul_nonneg (by positivity) hK
      · positivity
  · exact sub_nonneg.mpr hrate.2.le




theorem abs_sixVertexEvenChargeBetheOffset_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeBetheOffset hc s k j| <=
      Real.pi *
        (sixVertexFixedChargeDensityInvWidthConstant c 0 +
          sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) /
        (((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c) *
          sixVertexTailFiniteDensityFloor c) := by
  let N := sixVertexFourWidth (2 * s) k
  let t := 2 * s + k
  let p := sixVertexHalfFilledBetheRoots hc t
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let rho := sixVertexFourierPhysicalDensityMap hc
  let E0 := sixVertexFixedChargeDensityInvWidthConstant c 0
  let Er := sixVertexFixedChargeDensityInvWidthConstant c (2 * s)
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let floor := sixVertexTailFiniteDensityFloor c
  let i := sixVertexEvenChargeHalfIndex s k j
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwidth : sixVertexFourWidth 0 t = N := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hE0 : 0 <= E0 :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail 0
  have hEr : 0 <= Er :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail (2 * s)
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hpOpen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc t
  have hqOpen : SixVertexOpenRootSimplex q :=
    sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k
  have hpGauge : sixVertexWeightedFiniteDensityGauge hc N
      ((t + 1) + (t + 1)) p rho <= E0 / N := by
    have h := sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail
      hc htail t
    rw [hwidth] at h
    simpa [p, rho, E0, t, N,
      sixVertexFixedChargeDensityInvWidthConstant] using h
  have hqGauge : sixVertexWeightedFiniteDensityGauge hc N
      (sixVertexFixedChargeBetheParticleCount (2 * s) k) q rho <= Er / N := by
    simpa [q, rho, Er, N, sixVertexFixedChargeDensityInvWidthConstant] using
      sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail
        hc htail (2 * s) k
  have hpClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N ((t + 1) + (t + 1)) p x - rho x)| <=
          E0 / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p rho x hx).trans hpGauge
  have hqClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) q x - rho x)| <=
          Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q rho x hx).trans hqGauge
  have hiIcc : p i ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hpOpen.2.2 i).1.le, (hpOpen.2.2 i).2.le⟩
  have hcountBound :=
    abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose
      hc hN hpOpen.2.1 hqOpen.2.1 hE0 hEr hpClose hqClose hiIcc
  have hpSol : SixVertexSatisfiesBetheEquations c N
      ((t + 1) + (t + 1)) p := by
    rw [← hwidth]
    exact sixVertexHalfFilledBetheRoots_is_solution hc t
  have hqSol : SixVertexSatisfiesBetheEquations c N
      (sixVertexFixedChargeBetheParticleCount (2 * s) k) q :=
    sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k
  have hpAt := sixVertexBetheCountingFunction_at_root hN hpSol i
  have hqAt := sixVertexBetheCountingFunction_at_root hN hqSol j
  have hquantum := sixVertexEvenChargeHalfIndex_quantum s k j
  have hcountEq :
      sixVertexBetheCountingFunction c N ((t + 1) + (t + 1)) p (p i) =
        sixVertexBetheCountingFunction c N
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) q (q j) := by
    rw [hpAt, hqAt, hquantum]
  have hqDensity : ∀ x, floor <=
      sixVertexFiniteRootDensity c N
        (sixVertexFixedChargeBetheParticleCount (2 * s) k) q x := by
    intro x
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) q x
  have hlower :=
    lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub
      hc hN q hfloor.le hqDensity (a := p i) (b := q j)
  rw [← hcountEq] at hlower
  have hcombined : floor * |q j - p i| <=
      (((E0 + Er) / wmin) / N) * Real.pi := hlower.trans hcountBound
  have hdiff : |q j - p i| <=
      ((((E0 + Er) / wmin) / N) * Real.pi) / floor :=
    (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hcombined)
  have hmul := mul_le_mul_of_nonneg_left hdiff hNreal.le
  unfold sixVertexEvenChargeBetheOffset
  change |(N : Real) * (q j - p i)| <= _
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q j - p i| <=
        (N : Real) * (((((E0 + Er) / wmin) / N) * Real.pi) / floor) := hmul
    _ = Real.pi * (E0 + Er) / (wmin * floor) := by
      field_simp [hNreal.ne', hwmin.ne', hfloor.ne']

end

end StatMech.FrontierD
