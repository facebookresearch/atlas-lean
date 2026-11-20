/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOffsetNodal
import Code.FrontierD.SixVertexBetheOffsetNodalExplicit





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem tendsto_sixVertexCanonicalEvenOffsetNodalBound
    {c : Real} (hc : 2 < c) (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k =>
      sixVertexCanonicalEvenOffsetNodalError c hc s
          (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth (2 * s) k) (2 * s)
            (sixVertexCanonicalFixedEvenDensityFloor hc s) G D) /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s)
          (sixVertexCanonicalFixedEvenDensityFloor hc s))
      atTop (nhds 0) := by
  simpa using (tendsto_sixVertexCanonicalEvenOffsetNodalError hc s G D).div
    (tendsto_sixVertexCanonicalOffsetNetMargin (c := c)
      (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) (2 * s))
    (sixVertexFixedChargeOffsetContractionMargin_pos hc).ne'

theorem tendsto_sixVertexCanonicalOddOffsetNodalBound
    {c : Real} (hc : 2 < c) (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k =>
      sixVertexCanonicalOddOffsetNodalError c hc s
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
            (sixVertexCanonicalFixedOddDensityFloor hc s) G D) /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
          (sixVertexCanonicalFixedOddDensityFloor hc s))
      atTop (nhds 0) := by
  simpa using (tendsto_sixVertexCanonicalOddOffsetNodalError hc s G D).div
    (tendsto_sixVertexCanonicalOffsetNetMargin (c := c)
      (sixVertexCanonicalFixedOddDensityFloor_pos hc s) (2 * s + 1))
    (sixVertexFixedChargeOffsetContractionMargin_pos hc).ne'

theorem eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      forall i : Fin ((s + k + 1) + (s + k + 1)),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              ((s + k + 1) + (s + k + 1))
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) *
            sixVertexCanonicalEvenChargeOffset hc s k i -
          (2 * s : Real) * sixVertexContinuousOffsetFourier c hc
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)| <
          epsilon := by
  exact eventually_uniform_sixVertexCanonicalEvenDensityOffset hc s
    (lipschitzWith_sixVertexContinuousOffsetFourier hc)
    (abs_sixVertexContinuousOffsetFourier_le hc)
    (odd_sixVertexContinuousOffsetFourier hc)
    (sixVertexContinuousOffsetFourier_satisfiesEquation hc) hepsilon

theorem eventually_uniform_sixVertexCanonicalOddDensityOffset_fourier
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      forall i : Fin (((s + k + 1) + 1) + (s + k + 1)),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
              (((s + k + 1) + 1) + (s + k + 1))
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) *
            sixVertexCanonicalOddChargeOffset hc s k i -
          (2 * s + 1 : Real) * sixVertexContinuousOffsetFourier c hc
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)| <
          epsilon := by
  exact eventually_uniform_sixVertexCanonicalOddDensityOffset hc s
    (lipschitzWith_sixVertexContinuousOffsetFourier hc)
    (abs_sixVertexContinuousOffsetFourier_le hc)
    (odd_sixVertexContinuousOffsetFourier hc)
    (sixVertexContinuousOffsetFourier_satisfiesEquation hc) hepsilon

end

end StatMech.FrontierD
