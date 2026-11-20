/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedOffsetSymmetry
import Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalEvenOffsetUniformBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  Real.pi *
      (sixVertexHalfDensityInvWidthConstantOfLower c
          (sixVertexCanonicalHalfDensityFloor hc) +
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
          (sixVertexCanonicalFixedEvenDensityFloor hc s)) /
    (((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) *
      sixVertexCanonicalFixedEvenDensityFloor hc s)

def sixVertexCanonicalOddOffsetUniformBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  ((1 / 2 : Real) + Real.pi *
      (sixVertexHalfDensityInvWidthConstantOfLower c
          (sixVertexCanonicalHalfDensityFloor hc) +
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
          (sixVertexCanonicalFixedOddDensityFloor hc s)) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedOddDensityFloor hc s

private theorem nonneg_sixVertexHalfDensityInvWidthConstantOfLower
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) :
    0 <= sixVertexHalfDensityInvWidthConstantOfLower c lower := by
  unfold sixVertexHalfDensityInvWidthConstantOfLower
  apply div_nonneg
  · unfold sixVertexFiniteDensityContinuumErrorOfLower
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
    have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      positivity
    positivity
  · exact sub_nonneg.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

private theorem nonneg_sixVertexFixedChargeDensityInvWidthConstantOfLower
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) (r : Nat) :
    0 <= sixVertexFixedChargeDensityInvWidthConstantOfLower c r lower := by
  unfold sixVertexFixedChargeDensityInvWidthConstantOfLower
  apply div_nonneg
  · unfold sixVertexFixedChargeDensityStabilityErrorOfLower
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hscale := sixVertexRootDensityScale_pos hc
    have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
    have hK := sixVertexRootDensityKernelUniformBound_nonneg hc
    have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
    have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      positivity
    apply add_nonneg
    · apply add_nonneg
      · apply mul_nonneg hrate.1
        positivity
      · exact mul_nonneg (by positivity) hK
    · unfold sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      apply div_nonneg
      · exact add_nonneg (by positivity) (mul_nonneg (by positivity) hK)
      · positivity
  · exact sub_nonneg.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

theorem sixVertexCanonicalEvenOffsetUniformBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalEvenOffsetUniformBound c hc s := by
  unfold sixVertexCanonicalEvenOffsetUniformBound
  have hhalf := nonneg_sixVertexHalfDensityInvWidthConstantOfLower hc
    (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hfixed := nonneg_sixVertexFixedChargeDensityInvWidthConstantOfLower hc
    (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) (2 * s)
  have hw : 0 < (sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  exact div_nonneg (mul_nonneg Real.pi_pos.le (add_nonneg hhalf hfixed))
    (mul_nonneg hw.le (sixVertexCanonicalFixedEvenDensityFloor_pos hc s).le)

theorem sixVertexCanonicalOddOffsetUniformBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalOddOffsetUniformBound c hc s := by
  unfold sixVertexCanonicalOddOffsetUniformBound
  have hhalf := nonneg_sixVertexHalfDensityInvWidthConstantOfLower hc
    (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hfixed := nonneg_sixVertexFixedChargeDensityInvWidthConstantOfLower hc
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s) (2 * s + 1)
  have hw : 0 < (sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  exact div_nonneg
    (add_nonneg (by norm_num) (div_nonneg
      (mul_nonneg Real.pi_pos.le (add_nonneg hhalf hfixed)) hw.le))
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s).le

theorem eventually_abs_sixVertexCanonicalEvenChargeOffset_le
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      forall j, |sixVertexCanonicalEvenChargeOffset hc s k j| <=
        sixVertexCanonicalEvenOffsetUniformBound c hc s := by
  let r := 2 * s
  let E0 := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  let Er := sixVertexFixedChargeDensityInvWidthConstantOfLower c r
    (sixVertexCanonicalFixedEvenDensityFloor hc s)
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  have hshift : Tendsto (fun k : Nat => r + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s,
      eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth hc s,
      hshift.eventually (eventually_sixVertexCanonicalHalfDensityFloor_le hc),
      hshift.eventually
        (eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth hc)]
      with k hk hkgauge hhalfFloor hhalfGauge
  intro j
  let N := sixVertexFourWidth r k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (r + k)
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  have hwidth : sixVertexFourWidth 0 (r + k) = N := by
    dsimp [N, r]
    unfold sixVertexFourWidth
    omega
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hE0 : 0 <= E0 :=
    nonneg_sixVertexHalfDensityInvWidthConstantOfLower hc
      (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hEr : 0 <= Er :=
    nonneg_sixVertexFixedChargeDensityInvWidthConstantOfLower hc
      (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) r
  have hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          ((r + k + 1) + (r + k + 1)) p x -
            sixVertexFourierPhysicalDensityMap hc x)| <= E0 / N := by
    intro x hx
    rw [<- hwidth]
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p
      (sixVertexFourierPhysicalDensityMap hc) x hx).trans hhalfGauge
  have hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          ((s + k + 1) + (s + k + 1)) q x -
            sixVertexFourierPhysicalDensityMap hc x)| <= Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q
      (sixVertexFourierPhysicalDensityMap hc) x hx).trans hkgauge
  have hbound :=
    abs_width_mul_matchedBetheRoot_sub_le_of_weightedDensityClose
      hc hN (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (r + k))
      hk.1.1
      (by simpa [hwidth] using
        sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (r + k))
      hk.1.2.1 hE0 hEr (sixVertexCanonicalFixedEvenDensityFloor_pos hc s)
      hpClose hqClose hk.2 (sixVertexCanonicalEvenHalfIndex s k j) j
      (sixVertexCanonicalEvenHalfIndex_quantum s k j)
  simpa [sixVertexCanonicalEvenChargeOffset,
    sixVertexCanonicalEvenAlignedHalfRoots, p, q, N, E0, Er, lower,
    sixVertexCanonicalEvenOffsetUniformBound, r] using hbound

theorem eventually_abs_sixVertexCanonicalOddChargeOffset_le
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      forall j, |sixVertexCanonicalOddChargeOffset hc s k j| <=
        sixVertexCanonicalOddOffsetUniformBound c hc s := by
  let r := 2 * s + 1
  let E0 := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  let Er := sixVertexFixedChargeDensityInvWidthConstantOfLower c r
    (sixVertexCanonicalFixedOddDensityFloor hc s)
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  let B := ((1 / 2 : Real) + Real.pi * (E0 + Er) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) / lower
  have hshift : Tendsto (fun k : Nat => r + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s,
      eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth hc s,
      hshift.eventually (eventually_sixVertexCanonicalHalfDensityFloor_le hc),
      hshift.eventually
        (eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth hc)]
      with k hk hkgauge hhalfFloor hhalfGauge
  intro j
  let N := sixVertexFourWidth r k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (r + k)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  have hwidth : sixVertexFourWidth 0 (r + k) = N := by
    dsimp [N, r]
    unfold sixVertexFourWidth
    omega
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hE0 : 0 <= E0 :=
    nonneg_sixVertexHalfDensityInvWidthConstantOfLower hc
      (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hEr : 0 <= Er :=
    nonneg_sixVertexFixedChargeDensityInvWidthConstantOfLower hc
      (sixVertexCanonicalFixedOddDensityFloor_pos hc s) r
  have hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          ((r + k + 1) + (r + k + 1)) p x -
            sixVertexFourierPhysicalDensityMap hc x)| <= E0 / N := by
    intro x hx
    rw [<- hwidth]
    exact (abs_weightedFiniteDensity_sub_le_gauge hc p
      (sixVertexFourierPhysicalDensityMap hc) x hx).trans hhalfGauge
  have hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N
          (((s + k + 1) + 1) + (s + k + 1)) q x -
            sixVertexFourierPhysicalDensityMap hc x)| <= Er / N := by
    intro x hx
    exact (abs_weightedFiniteDensity_sub_le_gauge hc q
      (sixVertexFourierPhysicalDensityMap hc) x hx).trans hkgauge
  have hqL : |sixVertexCentralQuantumNumber
      (sixVertexCanonicalOddLowerHalfIndex s k j) -
        sixVertexCentralQuantumNumber j| <= (1 / 2 : Real) := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp only [sixVertexCanonicalOddLowerHalfIndex, Fin.val_mk]
    push_cast
    ring_nf
    norm_num
  have hqU : |sixVertexCentralQuantumNumber
      (sixVertexCanonicalOddUpperHalfIndex s k j) -
        sixVertexCentralQuantumNumber j| <= (1 / 2 : Real) := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp only [sixVertexCanonicalOddUpperHalfIndex, Fin.val_mk]
    push_cast
    ring_nf
    norm_num
  have hL := abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose
    hc hN (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (r + k))
    hk.1.1
    (by simpa [hwidth] using
      sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (r + k))
    hk.1.2.1 hE0 hEr (sixVertexCanonicalFixedOddDensityFloor_pos hc s)
    (by norm_num) hpClose hqClose hk.2
    (sixVertexCanonicalOddLowerHalfIndex s k j) j hqL
  have hU := abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose
    hc hN (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (r + k))
    hk.1.1
    (by simpa [hwidth] using
      sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (r + k))
    hk.1.2.1 hE0 hEr (sixVertexCanonicalFixedOddDensityFloor_pos hc s)
    (by norm_num) hpClose hqClose hk.2
    (sixVertexCanonicalOddUpperHalfIndex s k j) j hqU
  have havg : |(N : Real) *
      (q j - (p (sixVertexCanonicalOddLowerHalfIndex s k j) +
        p (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2)| <= B := by
    rw [show (N : Real) * (q j -
        (p (sixVertexCanonicalOddLowerHalfIndex s k j) +
          p (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2) =
      (((N : Real) * (q j - p (sixVertexCanonicalOddLowerHalfIndex s k j))) +
        ((N : Real) * (q j - p (sixVertexCanonicalOddUpperHalfIndex s k j)))) / 2 by
      ring,
      abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)).trans
      (by dsimp [B]; linarith)
  simpa [sixVertexCanonicalOddChargeOffset,
    sixVertexCanonicalOddAlignedHalfRoots, p, q, N, E0, Er, lower, B,
    sixVertexCanonicalOddOffsetUniformBound, r] using havg

end

end StatMech.FrontierD
