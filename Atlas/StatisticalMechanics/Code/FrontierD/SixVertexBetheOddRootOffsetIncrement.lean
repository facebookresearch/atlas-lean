/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddRootOffsetBound
import Code.FrontierD.SixVertexBetheEvenRootOffsetIncrement





namespace StatMech.FrontierD

noncomputable section



theorem abs_sixVertexOddChargeBetheOffset_sub_le_invWidth_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat)
    (j0 j1 : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k))
    (hij : j1.val = j0.val + 1) :
    |sixVertexOddChargeBetheOffset hc s k j1 -
        sixVertexOddChargeBetheOffset hc s k j0| <=
      (sixVertexRootGapFirstOrderConstant c
          (sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) +
        sixVertexRootGapFirstOrderConstant c
          (sixVertexFixedChargeDensityInvWidthConstant c 0) +
        ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          sixVertexTailFiniteDensityFloor c ^ 2) *
          ((((1 / 2 : Real) + Real.pi *
              (sixVertexFixedChargeDensityInvWidthConstant c 0 +
                sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) /
              ((sixVertexAnisotropyMagnitude c - 1) /
                sixVertexRootDensityScale c)) /
              sixVertexTailFiniteDensityFloor c) +
            (1 / sixVertexTailFiniteDensityFloor c) / 2)) /
        sixVertexFourWidth (2 * s + 1) k := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let t := 2 * s + 1 + k
  let p := sixVertexHalfFilledBetheRoots hc t
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let rho := sixVertexFourierPhysicalDensity c hc
  let rhoMap := sixVertexFourierPhysicalDensityMap hc
  let E0 := sixVertexFixedChargeDensityInvWidthConstant c 0
  let Er := sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)
  let floor := sixVertexTailFiniteDensityFloor c
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let A0 := sixVertexRootGapFirstOrderConstant c E0
  let Ar := sixVertexRootGapFirstOrderConstant c Er
  let R := (sixVertexFiniteRootDensityLipschitzConstant c : Real) / floor ^ 2
  let C := ((1 / 2 : Real) + Real.pi * (E0 + Er) / wmin) / floor
  let B := C + (1 / floor) / 2
  let D := R * B
  let il0 := sixVertexOddChargeLowerHalfIndex s k j0
  let iu0 := sixVertexOddChargeUpperHalfIndex s k j0
  let il1 := sixVertexOddChargeLowerHalfIndex s k j1
  let iu1 := sixVertexOddChargeUpperHalfIndex s k j1
  let mid0 := (p il0 + p iu0) / 2
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwidth : sixVertexFourWidth 0 t = N := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hE0 : 0 <= E0 :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail 0
  have hEr : 0 <= Er :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail (2 * s + 1)
  have hpOpen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc t
  have hqOpen : SixVertexOpenRootSimplex q :=
    sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k
  have hpSol : SixVertexSatisfiesBetheEquations c N ((t + 1) + (t + 1)) p := by
    rw [← hwidth]
    exact sixVertexHalfFilledBetheRoots_is_solution hc t
  have hqSol : SixVertexSatisfiesBetheEquations c N
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q :=
    sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k
  have hpGauge : sixVertexWeightedFiniteDensityGauge hc N
      ((t + 1) + (t + 1)) p rhoMap <= E0 / N := by
    have h := sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail
      hc htail t
    rw [hwidth] at h
    simpa [p, rhoMap, E0, t, N,
      sixVertexFixedChargeDensityInvWidthConstant] using h
  have hqGauge : sixVertexWeightedFiniteDensityGauge hc N
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q rhoMap <= Er / N := by
    simpa [q, rhoMap, Er, N, sixVertexFixedChargeDensityInvWidthConstant] using
      sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail
        hc htail (2 * s + 1) k
  have hpClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N ((t + 1) + (t + 1)) p x - rho x)| <=
          E0 / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p rhoMap x hx).trans hpGauge
  have hqClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q x - rho x)| <=
          Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q rhoMap x hx).trans hqGauge
  have hil : il1.val = il0.val + 1 := by
    dsimp [il0, il1, sixVertexOddChargeLowerHalfIndex]
    omega
  have hiu : iu1.val = iu0.val + 1 := by
    dsimp [iu0, iu1, sixVertexOddChargeUpperHalfIndex]
    omega
  have hilu : iu0.val = il0.val + 1 := by
    dsimp [il0, iu0, sixVertexOddChargeLowerHalfIndex,
      sixVertexOddChargeUpperHalfIndex]
  have hqGap0 := abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    hc htail hN (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k)
    hqOpen hqSol j0 j1 hfloor
    (sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail
      ⟨(hqOpen.2.2 j0).1.le, (hqOpen.2.2 j0).2.le⟩)
    hEr hqClose hij
  have hpHalf : 2 * ((t + 1) + (t + 1)) <= N := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hpLowerGap0 := abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    hc htail hN hpHalf hpOpen hpSol il0 il1 hfloor
    (sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail
      ⟨(hpOpen.2.2 il0).1.le, (hpOpen.2.2 il0).2.le⟩)
    hE0 hpClose hil
  have hpUpperGap0 := abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    hc htail hN hpHalf hpOpen hpSol iu0 iu1 hfloor
    (sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail
      ⟨(hpOpen.2.2 iu0).1.le, (hpOpen.2.2 iu0).2.le⟩)
    hE0 hpClose hiu
  have hqGap : |(N : Real) * (q j1 - q j0) - 1 / rho (q j0)| <= Ar / N := by
    convert hqGap0 using 1
    dsimp [Ar, sixVertexRootGapFirstOrderConstant, floor, Er, rho]
    field_simp [hfloor.ne', hNreal.ne']
  have hpLowerGap : |(N : Real) * (p il1 - p il0) - 1 / rho (p il0)| <= A0 / N := by
    convert hpLowerGap0 using 1
    dsimp [A0, sixVertexRootGapFirstOrderConstant, floor, E0, rho]
    field_simp [hfloor.ne', hNreal.ne']
  have hpUpperGap : |(N : Real) * (p iu1 - p iu0) - 1 / rho (p iu0)| <= A0 / N := by
    convert hpUpperGap0 using 1
    dsimp [A0, sixVertexRootGapFirstOrderConstant, floor, E0, rho]
    field_simp [hfloor.ne', hNreal.ne']
  have hmesh := sixVertexBetheSolution_consecutiveSpacing_upper_tail
    hc htail hN hpHalf hpOpen hpSol il0 iu0 hilu
  have hmesh' : |p iu0 - p il0| <= (1 / floor) / N := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hpOpen.1 (by simpa [Fin.lt_def, hilu])).le)]
    calc
      p iu0 - p il0 <= 1 / ((N : Real) * floor) := hmesh
      _ = (1 / floor) / N := by field_simp [hfloor.ne', hNreal.ne']
  have hoff : |(N : Real) * (q j0 - mid0)| <= C := by
    have h := abs_sixVertexOddChargeBetheOffset_le_tail hc htail s k j0
    change |(N : Real) * (q j0 - mid0)| <= C at h
    exact h
  have hrootMid : |q j0 - mid0| <= C / N := by
    rw [abs_mul, abs_of_pos hNreal] at hoff
    exact (le_div_iff₀ hNreal).2 (by simpa [mul_comm] using hoff)
  have hmidLower : |mid0 - p il0| <= ((1 / floor) / 2) / N := by
    have heq : mid0 - p il0 = (p iu0 - p il0) / 2 := by
      dsimp [mid0]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |p iu0 - p il0| / 2 <= ((1 / floor) / N) / 2 := by gcongr
      _ = ((1 / floor) / 2) / N := by field_simp [hNreal.ne']
  have hmidUpper : |mid0 - p iu0| <= ((1 / floor) / 2) / N := by
    have heq : mid0 - p iu0 = -(p iu0 - p il0) / 2 := by
      dsimp [mid0]
      ring
    rw [heq, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |p iu0 - p il0| / 2 <= ((1 / floor) / N) / 2 := by gcongr
      _ = ((1 / floor) / 2) / N := by field_simp [hNreal.ne']
  have hrootLower : |q j0 - p il0| <= B / N := by
    calc
      |q j0 - p il0| <= |q j0 - mid0| + |mid0 - p il0| := abs_sub_le _ _ _
      _ <= C / N + ((1 / floor) / 2) / N := add_le_add hrootMid hmidLower
      _ = B / N := by dsimp [B]; ring
  have hrootUpper : |q j0 - p iu0| <= B / N := by
    calc
      |q j0 - p iu0| <= |q j0 - mid0| + |mid0 - p iu0| := abs_sub_le _ _ _
      _ <= C / N + ((1 / floor) / 2) / N := add_le_add hrootMid hmidUpper
      _ = B / N := by dsimp [B]; ring
  have hrecipLower := sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn
    hc htail
    ⟨(hqOpen.2.2 j0).1.le, (hqOpen.2.2 j0).2.le⟩
    ⟨(hpOpen.2.2 il0).1.le, (hpOpen.2.2 il0).2.le⟩
  have hrecipUpper := sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn
    hc htail
    ⟨(hqOpen.2.2 j0).1.le, (hqOpen.2.2 j0).2.le⟩
    ⟨(hpOpen.2.2 iu0).1.le, (hpOpen.2.2 iu0).2.le⟩
  have hmiddle : |1 / rho (q j0) -
      (1 / rho (p il0) + 1 / rho (p iu0)) / 2| <= D / N := by
    have heq : 1 / rho (q j0) -
          (1 / rho (p il0) + 1 / rho (p iu0)) / 2 =
        ((1 / rho (q j0) - 1 / rho (p il0)) +
          (1 / rho (q j0) - 1 / rho (p iu0))) / 2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |(1 / rho (q j0) - 1 / rho (p il0)) +
          (1 / rho (q j0) - 1 / rho (p iu0))| / 2 <=
        (|1 / rho (q j0) - 1 / rho (p il0)| +
          |1 / rho (q j0) - 1 / rho (p iu0)|) / 2 := by
            gcongr
            exact abs_add_le _ _
      _ <= (R * (B / N) + R * (B / N)) / 2 := by
        gcongr
        · exact hrecipLower.trans (mul_le_mul_of_nonneg_left hrootLower (by positivity))
        · exact hrecipUpper.trans (mul_le_mul_of_nonneg_left hrootUpper (by positivity))
      _ = D / N := by dsimp [D]; ring
  have hinc := abs_midpointAlignedOffsetIncrement_le hNreal
    hqGap hpLowerGap hpUpperGap hmiddle
  simpa [sixVertexOddChargeBetheOffset, N, q, p, il0, iu0, il1, iu1,
    Ar, A0, D, R, B, C, E0, Er, wmin, floor] using hinc

end

end StatMech.FrontierD
