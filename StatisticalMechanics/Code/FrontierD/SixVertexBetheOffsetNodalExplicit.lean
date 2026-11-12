/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuousOffsetEquation
import Code.FrontierD.SixVertexBetheOffsetProfileRegularity
import Code.FrontierD.SixVertexBetheOddOffsetNodalConvergence
import Code.FrontierD.SixVertexBetheEvenOffsetNodalNonperiodic





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexContinuousOffsetFourierBound (c : Real) : Real :=
  (sixVertexOffsetRapidityLipschitzNNReal
    (sixVertexAntiferroelectricLambda c) : Real) * Real.pi

theorem abs_sixVertexContinuousOffsetFourier_le
    {c : Real} (hc : 2 < c) (x : Real) :
    |sixVertexContinuousOffsetFourier c hc x| <=
      sixVertexContinuousOffsetFourierBound c := by
  let lam := sixVertexAntiferroelectricLambda c
  let alpha := sixVertexMomentumRapidity lam
    (sixVertexAntiferroelectricLambda_pos hc) x
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi
        (by linarith [Real.pi_pos]) x)).property
  have hzero : sixVertexOffsetRapidityProfile lam 0 = 0 := by
    simp [sixVertexOffsetRapidityProfile, sixVertexOffsetCorrectionTerm]
  have hlip := (lipschitzWith_sixVertexOffsetRapidityProfile hlam).dist_le_mul
    alpha 0
  rw [Real.dist_eq, Real.dist_eq, hzero, sub_zero, sub_zero] at hlip
  have habs : |alpha| <= Real.pi := abs_le.2 halpha
  unfold sixVertexContinuousOffsetFourier
  exact hlip.trans (mul_le_mul_of_nonneg_left habs (NNReal.coe_nonneg _))



theorem eventually_uniform_evenChargeDensityOffset_fourier
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k i) *
            sixVertexEvenChargeBetheOffset hc s k i -
          (2 * s : Real) * sixVertexContinuousOffsetFourier c hc
            (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| < epsilon := by
  exact eventually_uniform_evenChargeDensityOffset_nonperiodic
    hc htail s (lipschitzWith_sixVertexContinuousOffsetFourier hc)
    (abs_sixVertexContinuousOffsetFourier_le hc)
    (odd_sixVertexContinuousOffsetFourier hc)
    (sixVertexContinuousOffsetFourier_satisfiesEquation hc) hepsilon



theorem eventually_uniform_oddChargeDensityOffset_fourier
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) *
            sixVertexOddChargeBetheOffset hc s k i -
          (2 * s + 1 : Real) * sixVertexContinuousOffsetFourier c hc
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)| < epsilon := by
  exact eventually_uniform_oddChargeDensityOffset_nonperiodic
    hc htail s (lipschitzWith_sixVertexContinuousOffsetFourier hc)
    (abs_sixVertexContinuousOffsetFourier_le hc)
    (odd_sixVertexContinuousOffsetFourier hc)
    (sixVertexContinuousOffsetFourier_satisfiesEquation hc) hepsilon

end

end StatMech.FrontierD
