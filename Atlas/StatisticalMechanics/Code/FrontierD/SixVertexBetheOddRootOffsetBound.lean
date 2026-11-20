/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheEvenRootOffsetBound





namespace StatMech.FrontierD

noncomputable section




theorem abs_sixVertexOddChargeBetheOffset_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    |sixVertexOddChargeBetheOffset hc s k j| <=
      ((1 / 2 : Real) + Real.pi *
        (sixVertexFixedChargeDensityInvWidthConstant c 0 +
          sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) /
        sixVertexTailFiniteDensityFloor c := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let t := 2 * s + 1 + k
  let p := sixVertexHalfFilledBetheRoots hc t
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let rho := sixVertexFourierPhysicalDensityMap hc
  let E0 := sixVertexFixedChargeDensityInvWidthConstant c 0
  let Er := sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let floor := sixVertexTailFiniteDensityFloor c
  let il := sixVertexOddChargeLowerHalfIndex s k j
  let iu := sixVertexOddChargeUpperHalfIndex s k j
  let mid := (p il + p iu) / 2
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwidth : sixVertexFourWidth 0 t = N := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hE0 : 0 <= E0 :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail 0
  have hEr : 0 <= Er :=
    sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail (2 * s + 1)
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hpOpen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc t
  have hqOpen : SixVertexOpenRootSimplex q :=
    sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k
  have hpGauge : sixVertexWeightedFiniteDensityGauge hc N
      ((t + 1) + (t + 1)) p rho <= E0 / N := by
    have h := sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail
      hc htail t
    rw [hwidth] at h
    simpa [p, rho, E0, t, N,
      sixVertexFixedChargeDensityInvWidthConstant] using h
  have hqGauge : sixVertexWeightedFiniteDensityGauge hc N
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q rho <= Er / N := by
    simpa [q, rho, Er, N, sixVertexFixedChargeDensityInvWidthConstant] using
      sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail
        hc htail (2 * s + 1) k
  have hpClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N ((t + 1) + (t + 1)) p x - rho x)| <=
          E0 / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p rho x hx).trans hpGauge
  have hqClose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q x - rho x)| <=
          Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q rho x hx).trans hqGauge
  have hmidIcc : mid ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [mid]
    constructor
    · linarith [(hpOpen.2.2 il).1, (hpOpen.2.2 iu).1]
    · linarith [(hpOpen.2.2 il).2, (hpOpen.2.2 iu).2]
  have hcountBound :=
    abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose
      hc hN hpOpen.2.1 hqOpen.2.1 hE0 hEr hpClose hqClose hmidIcc
  have hpSol : SixVertexSatisfiesBetheEquations c N
      ((t + 1) + (t + 1)) p := by
    rw [← hwidth]
    exact sixVertexHalfFilledBetheRoots_is_solution hc t
  have hqSol : SixVertexSatisfiesBetheEquations c N
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q :=
    sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k
  have hpLowerAt := sixVertexBetheCountingFunction_at_root hN hpSol il
  have hpUpperAt := sixVertexBetheCountingFunction_at_root hN hpSol iu
  have hqAt := sixVertexBetheCountingFunction_at_root hN hqSol j
  have hpDensity : ∀ x, floor <=
      sixVertexFiniteRootDensity c N ((t + 1) + (t + 1)) p x := by
    intro x
    apply sixVertexTailFiniteDensityFloor_le hc hN
    · dsimp [N, t]
      unfold sixVertexFourWidth
      omega
  have hpMono := monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg
    hc hN p (fun x => (hpDensity x).trans' hfloor.le)
  have hiltiu : il < iu := by
    simp [il, iu, sixVertexOddChargeLowerHalfIndex,
      sixVertexOddChargeUpperHalfIndex]
  have hrootOrder : p il <= mid ∧ mid <= p iu := by
    have h := (hpOpen.1 hiltiu).le
    dsimp [mid]
    constructor <;> linarith
  have hmonoLower := hpMono hrootOrder.1
  have hmonoUpper := hpMono hrootOrder.2
  have hquantumAverage := sixVertexOddChargeHalfIndex_quantum_average s k j
  have hquantumGap :
      sixVertexCentralQuantumNumber iu - sixVertexCentralQuantumNumber il = 1 := by
    dsimp [il, iu]
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [sixVertexOddChargeLowerHalfIndex, sixVertexOddChargeUpperHalfIndex]
  have hmidQuantum :
      |sixVertexBetheCountingFunction c N ((t + 1) + (t + 1)) p mid -
        sixVertexCentralQuantumNumber j / N| <= 1 / (2 * N) := by
    rw [hpLowerAt] at hmonoLower
    rw [hpUpperAt] at hmonoUpper
    rw [abs_le]
    constructor
    · have havg :
          sixVertexCentralQuantumNumber j / (N : Real) =
            (sixVertexCentralQuantumNumber il / N +
              sixVertexCentralQuantumNumber iu / N) / 2 := by
          rw [← hquantumAverage]
          ring
      rw [havg]
      have hgap : sixVertexCentralQuantumNumber iu / (N : Real) -
          sixVertexCentralQuantumNumber il / N = 1 / N := by
        rw [← sub_div, hquantumGap]
      have hhalfGap : 1 / (2 * (N : Real)) = (1 / N) / 2 := by
        field_simp [hNreal.ne']
      linarith
    · have havg :
          sixVertexCentralQuantumNumber j / (N : Real) =
            (sixVertexCentralQuantumNumber il / N +
              sixVertexCentralQuantumNumber iu / N) / 2 := by
          rw [← hquantumAverage]
          ring
      rw [havg]
      have hgap : sixVertexCentralQuantumNumber iu / (N : Real) -
          sixVertexCentralQuantumNumber il / N = 1 / N := by
        rw [← sub_div, hquantumGap]
      have hhalfGap : 1 / (2 * (N : Real)) = (1 / N) / 2 := by
        field_simp [hNreal.ne']
      linarith
  have hqDensity : ∀ x, floor <=
      sixVertexFiniteRootDensity c N
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q x := by
    intro x
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k) q x
  have hlower :=
    lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub
      hc hN q hfloor.le hqDensity (a := mid) (b := q j)
  have hcountDiff :
      |sixVertexBetheCountingFunction c N
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q (q j) -
        sixVertexBetheCountingFunction c N
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q mid| <=
        1 / (2 * N) + (((E0 + Er) / wmin) / N) * Real.pi := by
    rw [hqAt]
    calc
      |sixVertexCentralQuantumNumber j / N -
          sixVertexBetheCountingFunction c N
            (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q mid| <=
        |sixVertexCentralQuantumNumber j / N -
          sixVertexBetheCountingFunction c N ((t + 1) + (t + 1)) p mid| +
        |sixVertexBetheCountingFunction c N ((t + 1) + (t + 1)) p mid -
          sixVertexBetheCountingFunction c N
            (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q mid| :=
        abs_sub_le _ _ _
      _ <= 1 / (2 * N) + (((E0 + Er) / wmin) / N) * Real.pi := by
        exact add_le_add (by simpa [abs_sub_comm] using hmidQuantum) hcountBound
  have hcombined : floor * |q j - mid| <=
      1 / (2 * N) + (((E0 + Er) / wmin) / N) * Real.pi :=
    hlower.trans hcountDiff
  have hright : 1 / (2 * (N : Real)) +
      (((E0 + Er) / wmin) / N) * Real.pi =
      ((1 / 2 : Real) + Real.pi * (E0 + Er) / wmin) / N := by
    field_simp [hNreal.ne', hwmin.ne']
  rw [hright] at hcombined
  have hdiff : |q j - mid| <=
      (((1 / 2 : Real) + Real.pi * (E0 + Er) / wmin) / N) / floor :=
    (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hcombined)
  have hmul := mul_le_mul_of_nonneg_left hdiff hNreal.le
  unfold sixVertexOddChargeBetheOffset
  change |(N : Real) * (q j - mid)| <= _
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q j - mid| <=
        (N : Real) *
          (((((1 / 2 : Real) + Real.pi * (E0 + Er) / wmin) / N) / floor)) := hmul
    _ = ((1 / 2 : Real) + Real.pi * (E0 + Er) / wmin) / floor := by
      field_simp [hNreal.ne', hwmin.ne', hfloor.ne']

end

end StatMech.FrontierD
