/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch
import Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch
import Code.FrontierD.SixVertexBetheCanonicalPerronDensity





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

noncomputable def sixVertexCanonicalFixedEvenDensityFloor
    {c : Real} (hc : 2 < c) (s : Nat) : Real :=
  Classical.choose
    (eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s)

theorem sixVertexCanonicalFixedEvenDensityFloor_pos
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 < sixVertexCanonicalFixedEvenDensityFloor hc s :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s)).1

def SixVertexCanonicalFixedEvenDensityWitness
    {c : Real} (hc : 2 < c) (s k : Nat)
    (p : Fin ((s + k + 1) + (s + k + 1)) -> Real) : Prop :=
  SixVertexFixedEvenChargePerronBranchWitness c s k p ∧
    forall x, sixVertexCanonicalFixedEvenDensityFloor hc s <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1)) p x

theorem eventually_exists_sixVertexCanonicalFixedEvenDensityWitness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexCanonicalFixedEvenDensityWitness hc s k p :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s)).2

noncomputable def sixVertexCanonicalFixedEvenDensityPerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin ((s + k + 1) + (s + k + 1)) -> Real := by
  classical
  exact if h : ∃ p, SixVertexCanonicalFixedEvenDensityWitness hc s k p then
    Classical.choose h
  else sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k

theorem eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexCanonicalFixedEvenDensityWitness hc s k
        (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) := by
  filter_upwards
    [eventually_exists_sixVertexCanonicalFixedEvenDensityWitness hc s]
      with k hk
  rw [sixVertexCanonicalFixedEvenDensityPerronBetheRoots, dif_pos hk]
  exact Classical.choose_spec hk

noncomputable def sixVertexCanonicalFixedOddDensityFloor
    {c : Real} (hc : 2 < c) (s : Nat) : Real :=
  Classical.choose
    (eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
      hc s)

theorem sixVertexCanonicalFixedOddDensityFloor_pos
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 < sixVertexCanonicalFixedOddDensityFloor hc s :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
      hc s)).1

def SixVertexCanonicalFixedOddDensityWitness
    {c : Real} (hc : 2 < c) (s k : Nat)
    (p : Fin (((s + k + 1) + 1) + (s + k + 1)) -> Real) : Prop :=
  SixVertexFixedOddChargePerronBranchWitness c s k p ∧
    forall x, sixVertexCanonicalFixedOddDensityFloor hc s <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1)) p x

theorem eventually_exists_sixVertexCanonicalFixedOddDensityWitness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexCanonicalFixedOddDensityWitness hc s k p :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
      hc s)).2

noncomputable def sixVertexCanonicalFixedOddDensityPerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (((s + k + 1) + 1) + (s + k + 1)) -> Real := by
  classical
  exact if h : ∃ p, SixVertexCanonicalFixedOddDensityWitness hc s k p then
    Classical.choose h
  else sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k

theorem eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexCanonicalFixedOddDensityWitness hc s k
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) := by
  filter_upwards
    [eventually_exists_sixVertexCanonicalFixedOddDensityWitness hc s]
      with k hk
  rw [sixVertexCanonicalFixedOddDensityPerronBetheRoots, dif_pos hk]
  exact Classical.choose_spec hk

def sixVertexFixedChargeDensityInvWidthConstantOfLower
    (c : Real) (r : Nat) (lower : Real) : Real :=
  sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower /
    (1 - sixVertexRootDensityContractionRate c)

theorem sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower
    {c : Real} (hc : 2 < c) {N q r : Nat} (hN : 0 < N) (hq : 0 < q)
    (hcharge : N = 2 * q + 2 * r) {p : Fin q -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N q p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
    sixVertexWeightedFiniteDensityGauge hc N q p
        (sixVertexFourierPhysicalDensityMap hc) <=
      sixVertexFixedChargeDensityInvWidthConstantOfLower c r lower / N := by
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p
    (sixVertexFourierPhysicalDensityMap hc)
  have hrateGap : 0 < 1 - rate :=
    sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have himprove : G <= rate * G +
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    exact sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
      hc hN hq hcharge hopen hsol
      (sixVertexFourierPhysicalDensityMap hc)
      (sixVertexFourierPhysicalDensity_continuumEquation hc)
      (intervalIntegral_sixVertexFourierPhysicalDensity hc)
      hlower hdensity (norm_nonneg _) le_rfl
  have hbasic : (1 - rate) * G <=
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    nlinarith
  have hbasic' : (1 - rate) * G <=
      sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N :=
    hbasic.trans_eq
      (sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
        c lower r hN)
  rw [mul_comm] at hbasic'
  have hdiv := (le_div_iff₀ hrateGap).2 hbasic'
  change sixVertexWeightedFiniteDensityGauge hc N q p
      (sixVertexFourierPhysicalDensityMap hc) <= _ at hdiv
  unfold sixVertexFixedChargeDensityInvWidthConstantOfLower
  dsimp [rate] at hdiv ⊢
  convert hdiv using 1
  field_simp [hrateGap.ne']

theorem eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
            (sixVertexCanonicalFixedEvenDensityFloor hc s) /
          sixVertexFourWidth (2 * s) k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower hc
    (sixVertexFourWidth_pos (2 * s) k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    hk.1.1 hk.1.2.1
    (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) hk.2

theorem eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
            (sixVertexCanonicalFixedOddDensityFloor hc s) /
          sixVertexFourWidth (2 * s + 1) k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower hc
    (sixVertexFourWidth_pos (2 * s + 1) k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    hk.1.1 hk.1.2.1
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s) hk.2

noncomputable def sixVertexCanonicalHalfDensityFloor
    {c : Real} (hc : 2 < c) : Real :=
  Classical.choose
    (eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc)

theorem sixVertexCanonicalHalfDensityFloor_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexCanonicalHalfDensityFloor hc :=
  (Classical.choose_spec
    (eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc)).1

theorem eventually_sixVertexCanonicalHalfDensityFloor_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, forall x,
      sixVertexCanonicalHalfDensityFloor hc <=
        sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k) x :=
  (Classical.choose_spec
    (eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc)).2

def sixVertexHalfDensityInvWidthConstantOfLower
    (c lower : Real) : Real :=
  sixVertexFiniteDensityContinuumErrorOfLower c 1 lower /
    (1 - sixVertexRootDensityContractionRate c)

theorem sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower
    {c : Real} (hc : 2 < c) {N q : Nat} (hN : 0 < N) (hq : 0 < q)
    (hhalf : N = 2 * q) {p : Fin q -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N q p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
    sixVertexWeightedFiniteDensityGauge hc N q p
        (sixVertexFourierPhysicalDensityMap hc) <=
      sixVertexHalfDensityInvWidthConstantOfLower c lower / N := by
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p
    (sixVertexFourierPhysicalDensityMap hc)
  have hrateGap : 0 < 1 - rate :=
    sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have himprove : G <= rate * G +
      sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    cases q with
    | zero => omega
    | succ n =>
        exact sixVertexWeightedFiniteDensityGauge_selfImproves hc hN
          (by omega) (by omega) hopen hsol
          (sixVertexFourierPhysicalDensityMap hc)
          (sixVertexFourierPhysicalDensity_continuumEquation hc)
          (intervalIntegral_sixVertexFourierPhysicalDensity hc)
          hlower hdensity (norm_nonneg _) le_rfl
  have hbasic : (1 - rate) * G <=
      sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    nlinarith
  have hbasic' : (1 - rate) * G <=
      sixVertexFiniteDensityContinuumErrorOfLower c 1 lower / N :=
    hbasic.trans_eq
      (sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div c lower hN)
  rw [mul_comm] at hbasic'
  have hdiv := (le_div_iff₀ hrateGap).2 hbasic'
  change sixVertexWeightedFiniteDensityGauge hc N q p
      (sixVertexFourierPhysicalDensityMap hc) <= _ at hdiv
  unfold sixVertexHalfDensityInvWidthConstantOfLower
  dsimp [rate] at hdiv ⊢
  convert hdiv using 1
  field_simp [hrateGap.ne']

theorem eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexHalfDensityInvWidthConstantOfLower c
            (sixVertexCanonicalHalfDensityFloor hc) /
          sixVertexFourWidth 0 k := by
  filter_upwards
    [eventually_sixVertexCanonicalHalfDensityFloor_le hc] with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower hc
    (sixVertexFourWidth_pos 0 k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
    (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k)
    (sixVertexCanonicalHalfDensityFloor_pos hc) hk

end

end StatMech.FrontierD
