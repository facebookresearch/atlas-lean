/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheEvenRootOffsetBound
import Code.FrontierD.SixVertexBethePhysicalDensityLipschitz





namespace StatMech.FrontierD

noncomputable section

def sixVertexRootGapFirstOrderConstant (c E : Real) : Real :=
  ((sixVertexFiniteRootDensityLipschitzConstant c : Real) *
      (1 / sixVertexTailFiniteDensityFloor c) ^ 2 +
    (1 / sixVertexTailFiniteDensityFloor c) *
      (E / ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c))) /
    sixVertexTailFiniteDensityFloor c



theorem abs_sixVertexEvenChargeBetheOffset_sub_le_invWidth_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat)
    (j0 j1 : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k))
    (hij : j1.val = j0.val + 1) :
    |sixVertexEvenChargeBetheOffset hc s k j1 -
        sixVertexEvenChargeBetheOffset hc s k j0| <=
      (sixVertexRootGapFirstOrderConstant c
          (sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) +
        sixVertexRootGapFirstOrderConstant c
          (sixVertexFixedChargeDensityInvWidthConstant c 0) +
        ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          sixVertexTailFiniteDensityFloor c ^ 2) *
          (Real.pi *
            (sixVertexFixedChargeDensityInvWidthConstant c 0 +
              sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) /
            (((sixVertexAnisotropyMagnitude c - 1) /
                sixVertexRootDensityScale c) *
              sixVertexTailFiniteDensityFloor c))) /
        sixVertexFourWidth (2 * s) k := by
  let N := sixVertexFourWidth (2 * s) k
  let t := 2 * s + k
  let p := sixVertexHalfFilledBetheRoots hc t
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let rho := sixVertexFourierPhysicalDensity c hc
  let rhoMap := sixVertexFourierPhysicalDensityMap hc
  let E0 := sixVertexFixedChargeDensityInvWidthConstant c 0
  let Er := sixVertexFixedChargeDensityInvWidthConstant c (2 * s)
  let floor := sixVertexTailFiniteDensityFloor c
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let A0 := sixVertexRootGapFirstOrderConstant c E0
  let Ar := sixVertexRootGapFirstOrderConstant c Er
  let R := (sixVertexFiniteRootDensityLipschitzConstant c : Real) / floor ^ 2
  let C := Real.pi * (E0 + Er) / (wmin * floor)
  let i0 := sixVertexEvenChargeHalfIndex s k j0
  let i1 := sixVertexEvenChargeHalfIndex s k j1
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
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
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail (2 * s)
  have hR : 0 <= R := by dsimp [R]; positivity
  have hpOpen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc t
  have hqOpen : SixVertexOpenRootSimplex q :=
    sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k
  have hpSol : SixVertexSatisfiesBetheEquations c N ((t + 1) + (t + 1)) p := by
    rw [← hwidth]
    exact sixVertexHalfFilledBetheRoots_is_solution hc t
  have hqSol : SixVertexSatisfiesBetheEquations c N
      (sixVertexFixedChargeBetheParticleCount (2 * s) k) q :=
    sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k
  have hpGauge : sixVertexWeightedFiniteDensityGauge hc N
      ((t + 1) + (t + 1)) p rhoMap <= E0 / N := by
    have h := sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail
      hc htail t
    rw [hwidth] at h
    simpa [p, rhoMap, E0, t, N,
      sixVertexFixedChargeDensityInvWidthConstant] using h
  have hqGauge : sixVertexWeightedFiniteDensityGauge hc N
      (sixVertexFixedChargeBetheParticleCount (2 * s) k) q rhoMap <= Er / N := by
    simpa [q, rhoMap, Er, N, sixVertexFixedChargeDensityInvWidthConstant] using
      sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail
        hc htail (2 * s) k
  have hpClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N ((t + 1) + (t + 1)) p x - rho x)| <=
          E0 / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p rhoMap x hx).trans hpGauge
  have hqClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) q x - rho x)| <=
          Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q rhoMap x hx).trans hqGauge
  have hi : i1.val = i0.val + 1 := by
    dsimp [i0, i1, sixVertexEvenChargeHalfIndex]
    omega
  have hqGap0 := abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    hc htail hN (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k)
    hqOpen hqSol j0 j1 hfloor
    (sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail
      ⟨(hqOpen.2.2 j0).1.le, (hqOpen.2.2 j0).2.le⟩)
    hEr hqClose hij
  have hpHalf : 2 * ((t + 1) + (t + 1)) <= N := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hpGap0 := abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail
    hc htail hN hpHalf hpOpen hpSol i0 i1 hfloor
    (sixVertexTailFiniteDensityFloor_le_fourierPhysicalDensity hc htail
      ⟨(hpOpen.2.2 i0).1.le, (hpOpen.2.2 i0).2.le⟩)
    hE0 hpClose hi
  have hqGap : |(N : Real) * (q j1 - q j0) - 1 / rho (q j0)| <= Ar / N := by
    convert hqGap0 using 1
    dsimp [Ar, sixVertexRootGapFirstOrderConstant, floor, Er, rho]
    field_simp [hfloor.ne', hNreal.ne']
  have hpGap : |(N : Real) * (p i1 - p i0) - 1 / rho (p i0)| <= A0 / N := by
    convert hpGap0 using 1
    dsimp [A0, sixVertexRootGapFirstOrderConstant, floor, E0, rho]
    field_simp [hfloor.ne', hNreal.ne']
  have hrecip := sixVertexFourierPhysicalDensity_reciprocal_lipschitzOn
    hc htail
    ⟨(hqOpen.2.2 j0).1.le, (hqOpen.2.2 j0).2.le⟩
    ⟨(hpOpen.2.2 i0).1.le, (hpOpen.2.2 i0).2.le⟩
  have hoff : |(N : Real) * (q j0 - p i0)| <= C := by
    have h := abs_sixVertexEvenChargeBetheOffset_le_tail hc htail s k j0
    change |(N : Real) * (q j0 - p i0)| <= C at h
    exact h
  have hinc := abs_alignedOffsetIncrement_le hNreal hR
    hqGap hpGap (by simpa [R, floor, rho] using hrecip) hoff
  simpa [sixVertexEvenChargeBetheOffset, N, q, p, i0, i1,
    Ar, A0, R, C, E0, Er, wmin, floor] using hinc

end

end StatMech.FrontierD
