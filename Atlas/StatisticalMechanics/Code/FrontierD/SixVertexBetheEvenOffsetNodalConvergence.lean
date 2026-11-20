/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheEvenOffsetNodalLimit








namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexFixedChargeOffsetNetMargin_eq
    (c : Real) (N r : Nat) :
    sixVertexFixedChargeOffsetNetMargin c N r =
      sixVertexFixedChargeOffsetContractionMargin c -
        sixVertexFixedChargeOffsetRowError c N r
          (sixVertexTailFiniteDensityFloor c) := by
  unfold sixVertexFixedChargeOffsetNetMargin
    sixVertexFixedChargeOffsetContractionMargin
  ring

theorem tendsto_sixVertexFixedChargeOffsetNetMargin
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    Tendsto (fun k => sixVertexFixedChargeOffsetNetMargin c
      (sixVertexFourWidth r k) r) atTop
      (nhds (sixVertexFixedChargeOffsetContractionMargin c)) := by
  have hconst : Tendsto
      (fun _ : Nat => sixVertexFixedChargeOffsetContractionMargin c)
      atTop (nhds (sixVertexFixedChargeOffsetContractionMargin c)) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_sixVertexFixedChargeOffsetRowError hc htail r)
  simpa [sixVertexFixedChargeOffsetNetMargin_eq] using h

theorem eventually_sixVertexFixedChargeOffsetNetMargin_ge_half
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexFixedChargeOffsetContractionMargin c / 2 <=
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth r k) r := by
  have hmargin := sixVertexFixedChargeOffsetContractionMargin_pos hc
  exact (tendsto_sixVertexFixedChargeOffsetNetMargin hc htail r).eventually
    (Ici_mem_nhds (by linarith))

theorem eventually_sixVertexFixedChargeOffsetNetMargin_pos
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      0 < sixVertexFixedChargeOffsetNetMargin c
        (sixVertexFourWidth r k) r := by
  have hmargin := sixVertexFixedChargeOffsetContractionMargin_pos hc
  filter_upwards
    [eventually_sixVertexFixedChargeOffsetNetMargin_ge_half hc htail r]
      with k hk
  exact (half_pos hmargin).trans_le hk

theorem tendsto_sixVertexEvenOffsetNodalError
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexEvenOffsetNodalError c s
      (sixVertexFourWidth (2 * s) k) G D) atTop (nhds 0) := by
  let r := 2 * s
  let lower := sixVertexTailFiniteDensityFloor c
  let B := sixVertexEvenOffsetUniformBound c s
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hresidual : Tendsto (fun k => sixVertexEvenOffsetResidualError c s
      (sixVertexFourWidth r k)) atTop (nhds 0) := by
    let C := 4 * sixVertexThetaTaylorBound c * B ^ 2
    have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
    simpa [sixVertexEvenOffsetResidualError, C, B] using hzero
  have hboundary : Tendsto (fun k => sixVertexEvenOffsetBoundaryError c s
      (sixVertexFourWidth r k)) atTop (nhds 0) := by
    let C := 2 * (s : Real) ^ 2 *
      (sixVertexThetaRightLipschitzNNReal c : Real) / lower
    have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
    convert hzero using 1
    funext k
    dsimp [C, lower]
    unfold sixVertexEvenOffsetBoundaryError
    field_simp [hlower.ne']
  have hsource : Tendsto (fun k => sixVertexEvenOffsetSourceMoveError c s
      (sixVertexFourWidth r k)) atTop (nhds 0) := by
    let C := (2 * s : Real) *
      (sixVertexThetaRightLipschitzNNReal c : Real) * B
    have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
    convert hzero using 1
    funext k
    dsimp [C, B]
    unfold sixVertexEvenOffsetSourceMoveError
    ring
  have htest := tendsto_sixVertexFixedChargeOffsetTestError c r hlower G D
  have htestScaled := htest.const_mul (2 * s : Real)
  simpa [sixVertexEvenOffsetNodalError, r, lower] using
    (((hresidual.add hboundary).add hsource).add htestScaled)

theorem tendsto_sixVertexEvenOffsetNodalBound
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k =>
      sixVertexEvenOffsetNodalError c s
          (sixVertexFourWidth (2 * s) k) G D /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s))
      atTop (nhds 0) := by
  have herror := tendsto_sixVertexEvenOffsetNodalError hc htail s G D
  have hmargin := tendsto_sixVertexFixedChargeOffsetNetMargin hc htail (2 * s)
  have hmarginPos := sixVertexFixedChargeOffsetContractionMargin_pos hc
  simpa using herror.div hmargin hmarginPos.ne'



theorem eventually_uniform_evenChargeDensityOffset
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauPeriodic : Function.Periodic tau (2 * Real.pi))
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∀ j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k j) *
            sixVertexEvenChargeBetheOffset hc s k j -
          (2 * s : Real) *
            tau (sixVertexFixedChargeBetheRoots hc (2 * s) k j)| < epsilon := by
  have hbound := tendsto_sixVertexEvenOffsetNodalBound hc htail s G D
  have hsmall : ∀ᶠ k : Nat in atTop,
      sixVertexEvenOffsetNodalError c s
          (sixVertexFourWidth (2 * s) k) G D /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s) < epsilon :=
    hbound.eventually (Iio_mem_nhds hepsilon)
  filter_upwards
    [eventually_sixVertexFixedChargeOffsetNetMargin_pos hc htail (2 * s),
      hsmall] with k hkmargin hksmall
  intro j
  exact (abs_evenChargeDensityOffset_sub_continuous_le_tail hc htail s k
    htauLip htauPeriodic htauBound htauOdd htauEq hkmargin j).trans_lt hksmall

end

end StatMech.FrontierD
