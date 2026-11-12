/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Code.FrontierD.SixVertexBetheOffsetLinearBound





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

private theorem halfDensityInvWidthConstant_nonneg
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

private theorem fixedDensityInvWidthConstant_nonneg
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
    · exact add_nonneg (mul_nonneg hrate.1 (by positivity))
        (mul_nonneg (by positivity) hK)
    · unfold sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      exact div_nonneg (add_nonneg (by positivity)
        (mul_nonneg (by positivity) hK)) (by positivity)
  · exact sub_nonneg.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

def sixVertexCanonicalEvenOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  ((sixVertexHalfDensityInvWidthConstantOfLower c
        (sixVertexCanonicalHalfDensityFloor hc) +
      sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
        (sixVertexCanonicalFixedEvenDensityFloor hc s)) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedEvenDensityFloor hc s

theorem sixVertexCanonicalEvenOffsetLinearBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalEvenOffsetLinearBound c hc s := by
  unfold sixVertexCanonicalEvenOffsetLinearBound
  have hhalf : 0 <= sixVertexHalfDensityInvWidthConstantOfLower c
      (sixVertexCanonicalHalfDensityFloor hc) :=
    halfDensityInvWidthConstant_nonneg hc
      (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hfixed : 0 <=
      sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
        (sixVertexCanonicalFixedEvenDensityFloor hc s) :=
    fixedDensityInvWidthConstant_nonneg hc
      (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) (2 * s)
  have hw : 0 < (sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  exact div_nonneg (div_nonneg (add_nonneg hhalf hfixed) hw.le)
    (sixVertexCanonicalFixedEvenDensityFloor_pos hc s).le


theorem eventually_abs_sixVertexCanonicalEvenChargeOffset_le_mul_abs_aligned
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop, forall j,
      |sixVertexCanonicalEvenChargeOffset hc s k j| <=
        sixVertexCanonicalEvenOffsetLinearBound c hc s *
          |sixVertexCanonicalEvenAlignedHalfRoots hc s k j| := by
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
  have hE0 : 0 <= E0 := halfDensityInvWidthConstant_nonneg hc
    (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hEr : 0 <= Er := fixedDensityInvWidthConstant_nonneg hc
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
  have hbound := abs_alignedBetheRootOffset_le_mul_abs hc hN
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (r + k))
    hk.1.1
    (by simpa [hwidth] using
      sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (r + k))
    hk.1.2.1 hE0 hEr
    (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) hk.2
    hpClose hqClose (sixVertexCanonicalEvenHalfIndex s k j) j
    (sixVertexCanonicalEvenHalfIndex_quantum s k j)
  simpa [sixVertexCanonicalEvenChargeOffset,
    sixVertexCanonicalEvenAlignedHalfRoots,
    sixVertexCanonicalEvenOffsetLinearBound, p, q, N, E0, Er, lower, r]
    using hbound

end

end StatMech.FrontierD
