/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheUniqueStabilitySheet
import Code.FrontierD.SixVertexBetheEventualPerron





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEventuallyHasSymmetricBetheIdentification_of_densityTail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    SixVertexEventuallyHasSymmetricBetheIdentification hc := by
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
  let btarget := c + 1
  have hctarget : c ∈ Set.Icc a btarget := by
    dsimp [btarget]
    exact ⟨hac.le, by linarith⟩
  have htargetTendsto := tendsto_sixVertexHalfFilledContinuationGauge
    ha hctarget htail
  have htargetGauge : ∀ᶠ k : Nat in atTop,
      sixVertexContinuationWeightedFiniteDensityGauge ha
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
          (sixVertexFourierPhysicalDensityFamily ha)
          (sixVertexHalfFilledBetheContinuationPoint ha hctarget k) < outer :=
    htargetTendsto.eventually (Iio_mem_nhds houterPos)
  filter_upwards [hmarginsK, htargetGauge] with k hkMargins hkTarget
  have hbaseGauge := eventually_sixVertexHalfFilledContinuationGauge_lt
    ha houterPos k
  have hcand := eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero k
  obtain ⟨c₀, hc₀Gauge, hc₀Cand, hc₀large⟩ :=
    (hbaseGauge.and (hcand.and
      (eventually_ge_atTop
        (max (c + 1) (2 * (((k + 1) + (k + 1) : Nat) : Real) + 5))))).exists
  let b := c₀ + 1
  have hc₀c : c + 1 ≤ c₀ := (le_max_left (c + 1) _).trans hc₀large
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  let z₀ := sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k
  let z₁ := sixVertexHalfFilledBetheContinuationPoint ha hcIcc k
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexFourierPhysicalDensityFamily ha) z₀ < outer :=
    hc₀Gauge b hc₀Icc
  have hz₁g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexFourierPhysicalDensityFamily ha) z₁ < outer := by
    rw [sixVertexHalfFilledContinuationGauge_eq_tailDistance ha hcIcc htail]
    rw [sixVertexHalfFilledContinuationGauge_eq_tailDistance ha hctarget htail] at hkTarget
    exact hkTarget
  have htailBase : ((((k + 1) + (k + 1) : Nat) : Real)) <
      sixVertexAnisotropyMagnitude c₀ := by
    have hlarge := (le_max_right (c + 1)
      (2 * (((k + 1) + (k + 1) : Nat) : Real) + 5)).trans hc₀large
    unfold sixVertexAnisotropyMagnitude sixVertexDelta
    nlinarith [sq_nonneg (c₀ -
      (2 * (((k + 1) + (k + 1) : Nat) : Real) + 5))]
  have hbaseKernel : sixVertexSymmetricBetheEigenvalueKernel c₀
      (sixVertexEvenPositiveHalfProjection (k + 1) z₀.1.2) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c₀ := by
    have hq : sixVertexEvenPositiveHalfProjection (k + 1) z₀.1.2 =
        sixVertexPositiveHalfBetheRoots (ha.trans hc₀Ioo.1) k := by rfl
    rw [hq, sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · exact (hc₀Cand (ha.trans hc₀Ioo.1)).1
    · intro j
      exact ⟨sixVertexPositiveHalfBetheRoots_pos (ha.trans hc₀Ioo.1) k j,
        sixVertexPositiveHalfBetheRoots_lt_pi (ha.trans hc₀Ioo.1) k j⟩
  have htargetKernel :=
    sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailDensityGauge
      ha (by dsimp [b]; linarith) hc₀Icc hcIcc hc₀Ioo hcIoo
      (m := k + 1) (by omega) (sixVertexFourWidth_pos 0 k) (by
        unfold sixVertexFourWidth
        omega)
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
      z₀ z₁ hz₀g hz₁g
      (sixVertexHalfFilledBetheContinuationPoint_projection ha hc₀Icc k)
      (sixVertexHalfFilledBetheContinuationPoint_projection ha hcIcc k)
      htailBase hbaseKernel (hc₀Cand (ha.trans hc₀Ioo.1)).2
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  have hvalue : sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c := by
    have hq : sixVertexEvenPositiveHalfProjection (k + 1) z₁.1.2 =
        sixVertexPositiveHalfBetheRoots hc k := by rfl
    rw [← hq, ← sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · exact htargetKernel
    · intro j
      rw [hq]
      exact ⟨sixVertexPositiveHalfBetheRoots_pos hc k j,
        sixVertexPositiveHalfBetheRoots_lt_pi hc k j⟩
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero, hhalf] using hvalue.symm

end

end StatMech.FrontierD
