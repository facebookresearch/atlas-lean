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

private theorem halfDensityInvWidthConstant_nonneg_odd
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
  · exact sub_nonneg.mpr
      (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

private theorem fixedDensityInvWidthConstant_nonneg_odd
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
  · exact sub_nonneg.mpr
      (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

def sixVertexCanonicalOddOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  let E0 := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  let Er := sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
    (sixVertexCanonicalFixedOddDensityFloor hc s)
  ((E0 + Er) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedOddDensityFloor hc s

def sixVertexCanonicalOddOffsetRemainderBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
    (4 * sixVertexCanonicalHalfDensityFloor hc ^ 2 *
      sixVertexCanonicalFixedOddDensityFloor hc s)

theorem sixVertexCanonicalOddOffsetLinearBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalOddOffsetLinearBound c hc s := by
  unfold sixVertexCanonicalOddOffsetLinearBound
  have hE0 : 0 <= sixVertexHalfDensityInvWidthConstantOfLower c
      (sixVertexCanonicalHalfDensityFloor hc) :=
    halfDensityInvWidthConstant_nonneg_odd hc
      (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hEr : 0 <= sixVertexFixedChargeDensityInvWidthConstantOfLower c
      (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s) :=
    fixedDensityInvWidthConstant_nonneg_odd hc
      (sixVertexCanonicalFixedOddDensityFloor_pos hc s) (2 * s + 1)
  have hw : 0 < (sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  exact div_nonneg (div_nonneg (add_nonneg hE0 hEr) hw.le)
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s).le

theorem sixVertexCanonicalOddOffsetRemainderBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalOddOffsetRemainderBound c hc s := by
  unfold sixVertexCanonicalOddOffsetRemainderBound
  exact div_nonneg (NNReal.coe_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num)
      (sq_nonneg (sixVertexCanonicalHalfDensityFloor hc)))
      (sixVertexCanonicalFixedOddDensityFloor_pos hc s).le)

private theorem abs_canonicalOddChargeOffset_le_linear_add
    {c : Real} (hc : 2 < c) (s k : Nat)
    {EP EQ lowerP lowerQ : Real}
    (hEP : 0 <= EP) (hEQ : 0 <= EQ)
    (hlowerP : 0 < lowerP) (hlowerQ : 0 < lowerQ)
    (hhalfLower : forall x, lowerP <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (hfixedLower : forall x, lowerQ <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) x)
    (hhalfClose : forall y, y ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y -
            sixVertexFourierPhysicalDensityMap hc y)| <=
        EP / sixVertexFourWidth (2 * s + 1) k)
    (hfixedClose : forall y, y ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c y *
        (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) y -
            sixVertexFourierPhysicalDensityMap hc y)| <=
        EQ / sixVertexFourWidth (2 * s + 1) k)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    |sixVertexCanonicalOddChargeOffset hc s k j| <=
      ((EP + EQ) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / lowerQ *
        |sixVertexCanonicalOddAlignedHalfRoots hc s k j| +
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (4 * lowerP ^ 2 * lowerQ * sixVertexFourWidth (2 * s + 1) k) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let np := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let nq := ((s + k + 1) + 1) + (s + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let il := sixVertexCanonicalOddLowerHalfIndex s k j
  let iu := sixVertexCanonicalOddUpperHalfIndex s k j
  let pl := p il
  let pu := p iu
  let a := (pl + pu) / 2
  let Fp := sixVertexBetheCountingFunction c N np p
  let Fq := sixVertexBetheCountingFunction c N nq q
  let gap := pu - pl
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let C := ((EP + EQ) / wmin) / (N : Real)
  let L : Real := sixVertexFiniteRootDensityLipschitzConstant c
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hnp : np <= N := by
    dsimp [np, N]
    unfold sixVertexFourWidth
    omega
  have hpOpen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (2 * s + 1 + k)
  have hqOpen : SixVertexOpenRootSimplex q := hfixed.1.1
  have hpSol : SixVertexSatisfiesBetheEquations c N np p := by
    dsimp [N, np, p]
    simpa [sixVertexFourWidth] using
      sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (2 * s + 1 + k)
  have hqSol : SixVertexSatisfiesBetheEquations c N nq q := hfixed.1.2.1
  have hplpu : pl <= pu := by
    exact (hpOpen.1 (by
      dsimp [il, iu, sixVertexCanonicalOddLowerHalfIndex,
        sixVertexCanonicalOddUpperHalfIndex]
      simp [Fin.lt_iff_val_lt_val])).le
  have hgap : 0 <= gap := sub_nonneg.mpr hplpu
  have haIcc : a ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [a]
    constructor
    · linarith [(hpOpen.2.2 il).1, (hpOpen.2.2 iu).1]
    · linarith [(hpOpen.2.2 il).2, (hpOpen.2.2 iu).2]
  have hcount := abs_sixVertexBetheCountingFunction_sub_le_mul_abs
    hc hN hpOpen.2.1 hqOpen.2.1 hEP hEQ
    (by simpa [N, np, p] using hhalfClose)
    (by simpa [N, nq, q] using hfixedClose) haIcc
  have hmid := abs_sixVertexBetheCountingFunction_midpoint_defect_le
    hc hN hnp p hplpu
  change |(Fp pl + Fp pu) / 2 - Fp a| <= L * gap ^ 2 / 4 at hmid
  have hpLRoot := sixVertexBetheCountingFunction_at_root hN hpSol il
  have hpURoot := sixVertexBetheCountingFunction_at_root hN hpSol iu
  have hqRoot := sixVertexBetheCountingFunction_at_root hN hqSol j
  have hquantum := sixVertexCanonicalOddHalfIndex_quantum_average s k j
  have hrootAverage : Fq (q j) = (Fp pl + Fp pu) / 2 := by
    dsimp [Fp, Fq, pl, pu]
    rw [hqRoot, hpLRoot, hpURoot, <- hquantum]
    ring
  have hcount' : |Fp a - Fq a| <= C * |a| := by
    simpa [Fp, Fq, C, wmin, N, np, nq, p, q] using hcount
  have hFdiff : |Fq (q j) - Fq a| <= C * |a| + L * gap ^ 2 / 4 := by
    rw [hrootAverage]
    calc
      |(Fp pl + Fp pu) / 2 - Fq a| <=
          |(Fp pl + Fp pu) / 2 - Fp a| + |Fp a - Fq a| :=
        abs_sub_le _ _ _
      _ <= L * gap ^ 2 / 4 + C * |a| := add_le_add hmid hcount'
      _ = C * |a| + L * gap ^ 2 / 4 := add_comm _ _
  have hfixedInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN q a (q j)
  have hfixedLowerInt := lower_mul_abs_sub_le_abs_intervalIntegral
    (continuous_sixVertexFiniteRootDensity hc N nq q)
    (by simpa [N, nq, q] using hfixedLower) hlowerQ.le
    (a := a) (b := q j)
  rw [hfixedInt] at hfixedLowerInt
  change lowerQ * |q j - a| <= |Fq (q j) - Fq a| at hfixedLowerInt
  have hdisplacement : lowerQ * |q j - a| <=
      C * |a| + L * gap ^ 2 / 4 := hfixedLowerInt.trans hFdiff
  have hhalfInt := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p pl pu
  have hquantumDiff : sixVertexCentralQuantumNumber iu -
      sixVertexCentralQuantumNumber il = 1 := by
    dsimp [il, iu, sixVertexCanonicalOddLowerHalfIndex,
      sixVertexCanonicalOddUpperHalfIndex]
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp
  have hhalfMass :
      (∫ x in pl..pu, sixVertexFiniteRootDensity c N np p x) = 1 / N := by
    rw [hhalfInt]
    dsimp [pl, pu]
    rw [hpLRoot, hpURoot, <- sub_div, hquantumDiff]
  have hhalfLowerInt := lower_mul_abs_sub_le_abs_intervalIntegral
    (continuous_sixVertexFiniteRootDensity hc N np p)
    (by simpa [N, np, p] using hhalfLower) hlowerP.le
    (a := pl) (b := pu)
  rw [hhalfMass, abs_of_nonneg (by positivity : (0 : Real) <= 1 / N),
    abs_of_nonneg hgap] at hhalfLowerInt
  have hgapBound : gap <= 1 / (lowerP * N) := by
    rw [show 1 / (lowerP * (N : Real)) =
      (1 / (N : Real)) / lowerP by
        field_simp [hNreal.ne', hlowerP.ne']]
    exact (le_div_iff₀ hlowerP).2
      (by simpa [mul_comm] using hhalfLowerInt)
  have hgapSq : gap ^ 2 <= (1 / (lowerP * N)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (lowerP * N) - gap)]
  have hL : 0 <= L := by dsimp [L]; exact NNReal.coe_nonneg _
  have hdisp' : |q j - a| <=
      (C * |a| + L * gap ^ 2 / 4) / lowerQ :=
    (le_div_iff₀ hlowerQ).2 (by simpa [mul_comm] using hdisplacement)
  unfold sixVertexCanonicalOddChargeOffset
  change |(N : Real) * (q j - a)| <= _
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q j - a| <=
        (N : Real) * ((C * |a| + L * gap ^ 2 / 4) / lowerQ) :=
      mul_le_mul_of_nonneg_left hdisp' hNreal.le
    _ <= (N : Real) *
        ((C * |a| + L * (1 / (lowerP * N)) ^ 2 / 4) / lowerQ) := by
      gcongr
    _ = ((EP + EQ) / wmin) / lowerQ * |a| +
        L / (4 * lowerP ^ 2 * lowerQ * N) := by
      dsimp [C]
      field_simp [hNreal.ne', hlowerP.ne', hlowerQ.ne']
    _ = _ := by rfl



theorem eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop, forall j,
      |sixVertexCanonicalOddChargeOffset hc s k j| <=
        sixVertexCanonicalOddOffsetLinearBound c hc s *
          |sixVertexCanonicalOddAlignedHalfRoots hc s k j| +
        sixVertexCanonicalOddOffsetRemainderBound c hc s /
          sixVertexFourWidth (2 * s + 1) k := by
  let r := 2 * s + 1
  let E0 := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  let Er := sixVertexFixedChargeDensityInvWidthConstantOfLower c r
    (sixVertexCanonicalFixedOddDensityFloor hc s)
  let lowerP := sixVertexCanonicalHalfDensityFloor hc
  let lowerQ := sixVertexCanonicalFixedOddDensityFloor hc s
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
  have hE0 : 0 <= E0 :=
    halfDensityInvWidthConstant_nonneg_odd hc
      (sixVertexCanonicalHalfDensityFloor_pos hc)
  have hEr : 0 <= Er :=
    fixedDensityInvWidthConstant_nonneg_odd hc
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
  have hbound := abs_canonicalOddChargeOffset_le_linear_add hc s k
    hE0 hEr (sixVertexCanonicalHalfDensityFloor_pos hc)
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s)
    (by simpa [hwidth, p, r, lowerP] using hhalfFloor)
    (by simpa [q, lowerQ] using hk.2)
    (by simpa [N, p, r] using hpClose)
    (by simpa [N, q, r] using hqClose) hk j
  unfold sixVertexCanonicalOddOffsetLinearBound
    sixVertexCanonicalOddOffsetRemainderBound
  dsimp [E0, Er, lowerP, lowerQ, r] at hbound ⊢
  convert hbound using 1 <;> ring

end

end StatMech.FrontierD
