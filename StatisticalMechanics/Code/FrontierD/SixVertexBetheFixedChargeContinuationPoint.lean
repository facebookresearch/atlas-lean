/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
import Code.FrontierD.SixVertexBetheUniqueStabilitySheet

open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexFixedChargeBetheContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (r k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedChargeBetheRoots hc2 r k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedChargeBetheRoots_mem_open hc2 r k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff (sixVertexFourWidth_pos r k) p).mpr
      (sixVertexFixedChargeBetheRoots_is_solution hc2 r k)

@[simp] theorem sixVertexFixedChargeBetheContinuationPoint_parameter
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (r k : Nat) :
    (sixVertexFixedChargeBetheContinuationPoint ha hc r k).1.1 = c := rfl

theorem sixVertexFixedChargeBetheContinuationPoint_roots
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (r k : Nat) :
    (sixVertexFixedChargeBetheContinuationPoint ha hc r k).1.2 =
      sixVertexFixedChargeBetheRoots (ha.trans_le hc.1) r k := rfl

@[simp] theorem sixVertexFixedChargeBetheContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (r k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexFixedChargeBetheContinuationPoint ha hc r k) = ⟨c, hc⟩ := rfl



theorem sixVertexFixedChargeContinuationGauge_le_anisotropyError
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (r k : Nat) :
    sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexFixedChargeBetheContinuationPoint ha hc r k) ≤
      ((1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) +
        (r : Real) / sixVertexFourWidth r k) / (2 * Real.pi) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  unfold sixVertexContinuationWeightedFiniteDensityGauge
  apply sixVertexWeightedFiniteDensityGauge_le_fixedChargeAnisotropyError
    hc2 (sixVertexFourWidth_pos r k)
  · rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  · exact sixVertexFourierPhysicalDensityFamily_continuumEquation ha ⟨c, hc⟩
  · exact intervalIntegral_sixVertexFourierPhysicalDensityFamily ha ⟨c, hc⟩
  · intro y hy
    exact (sixVertexFourierPhysicalDensityFamily_pos ha (⟨c, hc⟩, y)).le

theorem sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
    {c : Real} (hc : 2 < c) {N q r : Nat} (hN : 0 < N) (hq : 0 < q)
    (hcharge : N = 2 * q + 2 * r) {p : Fin q → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N q p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N q p x)
    (hE : 0 ≤ E)
    (hgauge : sixVertexWeightedFiniteDensityGauge hc N q p rho ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N q p rho ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
  cases q with
  | zero => omega
  | succ n =>
      exact sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge
        hc hN hcharge hopen hsol rho hrhoEq hrhoMass hlower hdensity hE hgauge





theorem sixVertexFixedChargeWeightedFiniteDensityGauge_le_invWidth_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r k : Nat) :
    sixVertexWeightedFiniteDensityGauge hc
        (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFourierPhysicalDensityMap hc) ≤
      (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r
          (sixVertexTailFiniteDensityFloor c) /
        (1 - sixVertexRootDensityContractionRate c)) /
        sixVertexFourWidth r k := by
  let N := sixVertexFourWidth r k
  let q := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let rho := sixVertexFourierPhysicalDensityMap hc
  let lower := sixVertexTailFiniteDensityFloor c
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p rho
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hq : 0 < q := sixVertexFixedChargeBetheParticleCount_pos r k
  have hcharge : N = 2 * q + 2 * r := by
    dsimp [N, q]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hrateGap : 0 < 1 - rate := by
    exact sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N q p x := by
    intro x
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le r k) p x
  have himprove : G ≤ rate * G +
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    apply sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
      hc hN hq hcharge
    · exact sixVertexFixedChargeBetheRoots_mem_open hc r k
    · exact sixVertexFixedChargeBetheRoots_is_solution hc r k
    · exact sixVertexFourierPhysicalDensity_continuumEquation hc
    · exact intervalIntegral_sixVertexFourierPhysicalDensity hc
    · exact hlower
    · exact hdensity
    · exact norm_nonneg _
    · exact le_rfl
  have hbasic : (1 - rate) * G ≤
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    nlinarith
  have hbasic' : (1 - rate) * G ≤
      sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N :=
    hbasic.trans_eq
      (sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
        c lower r hN)
  have hdiv : G ≤
      (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N) /
        (1 - rate) := (le_div_iff₀ hrateGap).2 (by
          simpa [mul_comm] using hbasic')
  change G ≤ _
  calc
    G ≤ (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N) /
        (1 - rate) := hdiv
    _ = (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower /
          (1 - rate)) / N := by
      field_simp [hrateGap.ne']




theorem sixVertexHalfFilledWeightedFiniteDensityGauge_le_invWidth_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) :
    sixVertexWeightedFiniteDensityGauge hc
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexHalfFilledBetheRoots hc k)
        (sixVertexFourierPhysicalDensityMap hc) ≤
      (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0
          (sixVertexTailFiniteDensityFloor c) /
        (1 - sixVertexRootDensityContractionRate c)) /
        sixVertexFourWidth 0 k := by
  let N := sixVertexFourWidth 0 k
  let q := (k + 1) + (k + 1)
  let p := sixVertexHalfFilledBetheRoots hc k
  let rho := sixVertexFourierPhysicalDensityMap hc
  let lower := sixVertexTailFiniteDensityFloor c
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p rho
  have hN : 0 < N := sixVertexFourWidth_pos 0 k
  have hq : 0 < q := by dsimp [q]; omega
  have hcharge : N = 2 * q + 2 * 0 := by
    dsimp [N, q]
    unfold sixVertexFourWidth
    omega
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hrateGap : 0 < 1 - rate := by
    exact sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N q p x := by
    intro x
    apply sixVertexTailFiniteDensityFloor_le hc hN
    · dsimp [N, q]
      unfold sixVertexFourWidth
      omega
  have himprove : G ≤ rate * G +
      sixVertexFixedChargeDensityStabilityErrorOfLower c N 0 lower := by
    apply sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
      hc hN hq hcharge
    · exact sixVertexHalfFilledBetheRoots_mem_open hc k
    · exact sixVertexHalfFilledBetheRoots_is_solution hc k
    · exact sixVertexFourierPhysicalDensity_continuumEquation hc
    · exact intervalIntegral_sixVertexFourierPhysicalDensity hc
    · exact hlower
    · exact hdensity
    · exact norm_nonneg _
    · exact le_rfl
  have hbasic : (1 - rate) * G ≤
      sixVertexFixedChargeDensityStabilityErrorOfLower c N 0 lower := by
    nlinarith
  have hbasic' : (1 - rate) * G ≤
      sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0 lower / N :=
    hbasic.trans_eq
      (sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
        c lower 0 hN)
  have hdiv : G ≤
      (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0 lower / N) /
        (1 - rate) := (le_div_iff₀ hrateGap).2 (by
          simpa [mul_comm] using hbasic')
  change G ≤ _
  calc
    G ≤ (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0 lower / N) /
        (1 - rate) := hdiv
    _ = (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 0 lower /
          (1 - rate)) / N := by
      field_simp [hrateGap.ne']



theorem tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    Tendsto (fun k : Nat =>
      sixVertexWeightedFiniteDensityGauge hc
        (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFourierPhysicalDensityMap hc)) atTop (nhds 0) := by
  let lower := sixVertexTailFiniteDensityFloor c
  let rate := sixVertexRootDensityContractionRate c
  let A := sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower /
    (1 - rate)
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hrateGap : 0 < 1 - rate := sub_pos.mpr hrate.2
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidthReal : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hupper : Tendsto (fun k : Nat => A / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidthReal
  apply squeeze_zero
  · intro k
    exact norm_nonneg _
  · intro k
    let N := sixVertexFourWidth r k
    let q := sixVertexFixedChargeBetheParticleCount r k
    let p := sixVertexFixedChargeBetheRoots hc r k
    let rho := sixVertexFourierPhysicalDensityMap hc
    let G := sixVertexWeightedFiniteDensityGauge hc N q p rho
    have hN : 0 < N := sixVertexFourWidth_pos r k
    have hq : 0 < q := sixVertexFixedChargeBetheParticleCount_pos r k
    have hcharge : N = 2 * q + 2 * r := by
      dsimp [N, q]
      rw [sixVertexFixedChargeBetheParticleCount_eq]
      unfold sixVertexFourWidth
      omega
    have hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N q p x := by
      intro x
      exact sixVertexTailFiniteDensityFloor_le hc hN
        (sixVertexFixedChargeBetheParticleCount_twice_le r k) p x
    have himprove : G ≤ rate * G +
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
      apply sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
        hc hN hq hcharge
      · exact sixVertexFixedChargeBetheRoots_mem_open hc r k
      · exact sixVertexFixedChargeBetheRoots_is_solution hc r k
      · exact sixVertexFourierPhysicalDensity_continuumEquation hc
      · exact intervalIntegral_sixVertexFourierPhysicalDensity hc
      · exact hlower
      · exact hdensity
      · exact norm_nonneg _
      · exact le_rfl
    have hbasic : (1 - rate) * G ≤
        sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
      nlinarith
    have hbasic' : (1 - rate) * G ≤
        sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N :=
      hbasic.trans_eq
        (sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
          c lower r hN)
    have hdiv : G ≤
        (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N) /
          (1 - rate) := (le_div_iff₀ hrateGap).2 (by
            simpa [mul_comm] using hbasic')
    calc
      G ≤ (sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N) /
          (1 - rate) := hdiv
      _ = A / N := by
        dsimp [A]
        field_simp [hrateGap.ne']
  · exact hupper



theorem tendsto_sixVertexFixedChargeContinuationGauge_tail
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    Tendsto (fun k : Nat =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexFixedChargeBetheContinuationPoint ha hc r k))
      atTop (nhds 0) := by
  simpa [sixVertexContinuationWeightedFiniteDensityGauge,
    sixVertexContinuumDensitySection,
    sixVertexFixedChargeBetheContinuationPoint_roots,
    sixVertexFourierPhysicalDensityMap] using
      tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail
        (ha.trans_le hc.1) htail r



theorem eventually_sixVertexFixedChargeContinuationGauge_lt
    {a outer : Real} (ha : 2 < a) (r k : Nat)
    (hcharge : (r : Real) / sixVertexFourWidth r k <
      outer * (2 * Real.pi)) :
    ∀ᶠ c : Real in atTop, ∀ b (hc : c ∈ Set.Icc a b),
      sixVertexContinuationWeightedFiniteDensityGauge ha
          (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFourierPhysicalDensityFamily ha)
          (sixVertexFixedChargeBetheContinuationPoint ha hc r k) < outer := by
  have hlimit : Tendsto (fun c : Real =>
      ((1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) +
        (r : Real) / sixVertexFourWidth r k) / (2 * Real.pi))
      atTop (nhds (((r : Real) / sixVertexFourWidth r k) /
        (2 * Real.pi))) := by
    have hzero := tendsto_sixVertexAnisotropyGaugeError
    simpa only [add_div, zero_add] using hzero.add
      (tendsto_const_nhds : Tendsto (fun _ : Real =>
        ((r : Real) / sixVertexFourWidth r k) / (2 * Real.pi))
        atTop (nhds (((r : Real) / sixVertexFourWidth r k) /
          (2 * Real.pi))))
  have hlimlt : ((r : Real) / sixVertexFourWidth r k) /
      (2 * Real.pi) < outer := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    exact hcharge
  have hevent := hlimit.eventually (Iio_mem_nhds hlimlt)
  filter_upwards [eventually_ge_atTop a, hevent] with c hca herr
  intro b hc
  exact (sixVertexFixedChargeContinuationGauge_le_anisotropyError
    ha hc r k).trans_lt herr

end

end StatMech.FrontierD
