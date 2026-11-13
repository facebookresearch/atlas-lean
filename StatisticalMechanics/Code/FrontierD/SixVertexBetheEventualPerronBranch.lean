/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Code.FrontierD.SixVertexBetheAnalyticCandidateSheet










open Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem sixVertexWeightedFiniteDensityGauge_fourier_congr
    {c₁ c₂ : Real} (hc₁ : 2 < c₁) (hc₂ : 2 < c₂)
    (hc : c₁ = c₂) {N n : Nat} {p q : Fin n → Real} (hp : p = q) :
    sixVertexWeightedFiniteDensityGauge hc₁ N n p
        (sixVertexFourierPhysicalDensityMap hc₁) =
      sixVertexWeightedFiniteDensityGauge hc₂ N n q
        (sixVertexFourierPhysicalDensityMap hc₂) := by
  subst c₂
  subst q
  rfl




theorem eventually_exists_sixVertexHalfFilledBethePerronBranch
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      ∃ p : Fin ((k + 1) + (k + 1)) → Real,
        SixVertexOpenRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) p ∧
        sixVertexSymmetricBetheEigenvalueKernel c
            (sixVertexEvenPositiveHalfProjection (k + 1) p) =
          sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) (by
              unfold sixVertexFourWidth
              omega) c := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFiniteDensityContinuumErrorOfLower t
            (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi :=
    hwidth.eventually hmargins
  filter_upwards [hmarginsK] with k hkMargins
  have hbaseGauge := eventually_sixVertexHalfFilledContinuationGauge_lt
    ha houterPos k
  have hcand :=
    eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero k
  obtain ⟨c₀, hc₀Gauge, hc₀Cand, hc₀large⟩ :=
    (hbaseGauge.and (hcand.and (eventually_ge_atTop (c + 1)))).exists
  let b := c₀ + 1
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k) < outer :=
    hc₀Gauge b hc₀Icc
  obtain ⟨roots, _hrootsBase, hrootsData, _hrootsAnalytic, hperron,
      _hrootsGauge⟩ :=
    exists_sixVertexHalfFilledPerronSheet_of_densityGauge
      ha (by dsimp [b]; linarith) hc₀Ioo k
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
          sixVertexFourierPhysicalDensityFamily_apply] using
            hrho t.1 t.2.1 x)
      hio (fun t => houter t.1 t.2.1)
      (fun t => (hkMargins t.1 t.2.1).1)
      (fun t => (hkMargins t.1 t.2.1).2)
      hz₀g (hc₀Cand (ha.trans hc₀Ioo.1)).1
      (hc₀Cand (ha.trans hc₀Ioo.1)).2
  refine ⟨roots c, (hrootsData c hcIcc).1, (hrootsData c hcIcc).2, ?_⟩
  exact hperron hcIoo



def SixVertexHalfFilledPerronBranchWitness
    (c : Real) (k : Nat) (p : Fin ((k + 1) + (k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p ∧
    sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexEvenPositiveHalfProjection (k + 1) p) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c



def SixVertexHalfFilledPerronGaugeWitness
    {c : Real} (hc : 2 < c) (k : Nat) (epsilon : Real)
    (p : Fin ((k + 1) + (k + 1)) → Real) : Prop :=
  SixVertexHalfFilledPerronBranchWitness c k p ∧
    sixVertexWeightedFiniteDensityGauge hc
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p
      (sixVertexFourierPhysicalDensityMap hc) < epsilon




theorem eventually_exists_sixVertexHalfFilledPerronGaugeWitness
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k epsilon p := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoBase, hrhoBase, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  let rhoLower := min rhoBase epsilon
  have hrhoLower : 0 < rhoLower := lt_min hrhoBase hepsilon
  have hrhoLowerBase : rhoLower ≤ rhoBase := min_le_left _ _
  have hrhoLowerEpsilon : rhoLower ≤ epsilon := min_le_right _ _
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  have hfloorLe :
      (sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c ≤ 1 := by
    rw [div_le_one (sixVertexRootDensityScale_pos hc)]
    exact (sixVertexRootDensityScale_bounds hc).1
  have houterEpsilon : outer < epsilon := by
    have hout := houter c hac.le
    have hproduct : rhoLower *
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤ epsilon := by
      calc
        rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c) ≤ rhoLower * 1 := by
          gcongr
        _ ≤ epsilon := by simpa using hrhoLowerEpsilon
    nlinarith
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFiniteDensityContinuumErrorOfLower t
            (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi :=
    hwidth.eventually hmargins
  filter_upwards [hmarginsK] with k hkMargins
  have hbaseGauge := eventually_sixVertexHalfFilledContinuationGauge_lt
    ha houterPos k
  have hcand :=
    eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero k
  obtain ⟨c₀, hc₀Gauge, hc₀Cand, hc₀large⟩ :=
    (hbaseGauge.and (hcand.and (eventually_ge_atTop (c + 1)))).exists
  let b := c₀ + 1
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k) < outer :=
    hc₀Gauge b hc₀Icc
  obtain ⟨roots, _hrootsBase, hrootsData, _hrootsAnalytic, hperron,
      hrootsGauge⟩ :=
    exists_sixVertexHalfFilledPerronSheet_of_densityGauge
      ha (by dsimp [b]; linarith) hc₀Ioo k
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        exact hrhoLowerBase.trans (by
          simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
            sixVertexFourierPhysicalDensityFamily_apply] using
              hrho t.1 t.2.1 x))
      hio (fun t => houter t.1 t.2.1)
      (fun t => (hkMargins t.1 t.2.1).1)
      (fun t => (hkMargins t.1 t.2.1).2)
      hz₀g (hc₀Cand (ha.trans hc₀Ioo.1)).1
      (hc₀Cand (ha.trans hc₀Ioo.1)).2
  obtain ⟨z, hzg, hzparam, hzroots⟩ := hrootsGauge c hcIcc
  have hdirect : sixVertexWeightedFiniteDensityGauge hc
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (roots c)
      (sixVertexFourierPhysicalDensityMap hc) ≤ inner := by
    have hzg' : sixVertexWeightedFiniteDensityGauge
        (ha.trans_le z.2.1.1)
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) z.1.2
        (sixVertexFourierPhysicalDensityMap (ha.trans_le z.2.1.1)) ≤ inner := by
      simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      sixVertexFourierPhysicalDensityFamily_apply,
      sixVertexFourierPhysicalDensityMap] using hzg
    rw [sixVertexWeightedFiniteDensityGauge_fourier_congr
      (ha.trans_le z.2.1.1) hc hzparam hzroots] at hzg'
    exact hzg'
  refine ⟨roots c, ?_, hdirect.trans_lt (hio.trans houterEpsilon)⟩
  exact ⟨(hrootsData c hcIcc).1, (hrootsData c hcIcc).2, hperron hcIoo⟩




noncomputable def sixVertexCanonicalPerronBetheRoots
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + 1) + (k + 1)) → Real := by
  classical
  exact if h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p then
      Classical.choose h
    else
      sixVertexHalfFilledBetheRoots hc k

theorem sixVertexCanonicalPerronBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexOpenRootSimplex (sixVertexCanonicalPerronBetheRoots hc k) := by
  by_cases h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p
  · rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
    exact (Classical.choose_spec h).1
  · rw [sixVertexCanonicalPerronBetheRoots, dif_neg h]
    exact sixVertexHalfFilledBetheRoots_mem_open hc k

theorem sixVertexCanonicalPerronBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (sixVertexCanonicalPerronBetheRoots hc k) := by
  by_cases h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p
  · rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
    exact (Classical.choose_spec h).2.1
  · rw [sixVertexCanonicalPerronBetheRoots, dif_neg h]
    exact sixVertexHalfFilledBetheRoots_is_solution hc k

theorem eventually_sixVertexCanonicalPerronBetheRoots_witness
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      SixVertexHalfFilledPerronBranchWitness c k
        (sixVertexCanonicalPerronBetheRoots hc k) := by
  filter_upwards [eventually_exists_sixVertexHalfFilledBethePerronBranch hc]
    with k hk
  have h : ∃ p, SixVertexHalfFilledPerronBranchWitness c k p := hk
  rw [sixVertexCanonicalPerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h


def sixVertexCanonicalPerronPositiveHalfRoots
    {c : Real} (hc : 2 < c) (k : Nat) : Fin (k + 1) → Real :=
  sixVertexEvenPositiveHalfProjection (k + 1)
    (sixVertexCanonicalPerronBetheRoots hc k)

def sixVertexCanonicalPerronPositiveHalfRootFamily
    {c : Real} (hc : 2 < c) : SixVertexSymmetricHalfFilledRoots :=
  fun k => sixVertexCanonicalPerronPositiveHalfRoots hc k

theorem sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    sixVertexCanonicalPerronPositiveHalfRoots hc k j ∈ Set.Ioo 0 Real.pi := by
  apply sixVertexEvenSymmetricLift_positive_mem_Ioo
  unfold sixVertexCanonicalPerronPositiveHalfRoots
  rw [sixVertexEvenSymmetricLift_projection (k + 1)
    (sixVertexCanonicalPerronBetheRoots_mem_open hc k).2.1]
  exact sixVertexCanonicalPerronBetheRoots_mem_open hc k



theorem eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexLambdaAlongFour c 0 k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalPerronPositiveHalfRoots hc k) := by
  filter_upwards [eventually_sixVertexCanonicalPerronBetheRoots_witness hc]
    with k hk
  have hkernel : sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexCanonicalPerronPositiveHalfRoots hc k) =
      sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexCanonicalPerronPositiveHalfRoots hc k) :=
    sixVertexSymmetricBetheEigenvalueKernel_eq_value c _
      (sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo hc k)
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  unfold SixVertexHalfFilledPerronBranchWitness at hk
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero, hhalf] using hk.2.2.symm.trans hkernel


def sixVertexCanonicalPerronCandidateRate
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalPerronPositiveHalfRoots hc k)) /
    (sixVertexFourWidth 0 k : Real)

theorem sixVertexCanonicalPerronCandidateRate_eq_rootAverage
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexCanonicalPerronCandidateRate hc k =
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
  rw [sixVertexCanonicalPerronCandidateRate,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalPerronPositiveHalfRootFamily
  ring

theorem sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate
    {c : Real} (hc : 2 < c) :
    sixVertexCentralWidthRate c =ᶠ[atTop]
      sixVertexCanonicalPerronCandidateRate hc := by
  filter_upwards [eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue hc]
    with k hk
  unfold sixVertexCentralWidthRate sixVertexCanonicalPerronCandidateRate
  rw [hk]

theorem sixVertexCentralWidthRate_eventuallyEq_canonicalRootAverage
    {c : Real} (hc : 2 < c) :
    sixVertexCentralWidthRate c =ᶠ[atTop] fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
  filter_upwards
    [sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate hc]
      with k hk
  rw [hk, sixVertexCanonicalPerronCandidateRate_eq_rootAverage]

end

end StatMech.FrontierD
