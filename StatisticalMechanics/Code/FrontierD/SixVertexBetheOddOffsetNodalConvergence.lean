/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Code.FrontierD.SixVertexBetheEvenOffsetNodalConvergence
import Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem tendsto_sixVertexOddOffsetResidualError
    (c : Real) (s : Nat) :
    Tendsto (fun k => sixVertexOddOffsetResidualError c s
      (sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) := by
  let C := 4 * sixVertexThetaTaylorBound c *
    sixVertexOddOffsetUniformBound c s ^ 2
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto
      (fun k : Nat => C / (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  simpa [sixVertexOddOffsetResidualError, C] using hzero

theorem tendsto_sixVertexOddOffsetBoundaryError
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    Tendsto (fun k => sixVertexOddOffsetBoundaryError c s
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k))
      atTop (nhds 0) := by
  let r := 2 * s + 1
  let lower := sixVertexTailFiniteDensityFloor c
  let T := sixVertexThetaTaylorBound c
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hT : 0 <= T := by
    dsimp [T, sixVertexThetaTaylorBound, sixVertexThetaCrossLipschitzBound]
    exact add_nonneg (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
      (div_nonneg (sixVertexRootDensityKernelLipschitzBound_pos hc).le
        (div_nonneg
          (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)
          (sixVertexRootDensityScale_pos hc).le))
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  let C1 := (r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) / lower
  have hfirst : Tendsto (fun k =>
      (r : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
          (s + 2 : Real) /
        ((sixVertexFourWidth r k : Real) * lower)) atTop (nhds 0) := by
    have hzero : Tendsto
        (fun k : Nat => C1 / (sixVertexFourWidth r k : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
    convert hzero using 1
    funext k
    dsimp [C1]
    field_simp [hlower.ne']
  let C2 := T / lower ^ 2
  have hupper : Tendsto
      (fun k : Nat => C2 / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  have hsecond : Tendsto (fun k =>
      (sixVertexFixedChargeBetheParticleCount r k : Real) * T /
        (((sixVertexFourWidth r k : Real) * lower) ^ 2))
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun k => C2 / (sixVertexFourWidth r k : Real))
    · filter_upwards [] with k
      positivity
    · filter_upwards [] with k
      let N := sixVertexFourWidth r k
      let n := sixVertexFixedChargeBetheParticleCount r k
      have hN : 0 < N := sixVertexFourWidth_pos r k
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hnle : n <= N := by
        have htwice := sixVertexFixedChargeBetheParticleCount_twice_le r k
        omega
      have hnleReal : (n : Real) <= N := by exact_mod_cast hnle
      calc
        (n : Real) * T / (((N : Real) * lower) ^ 2) <=
            (N : Real) * T / (((N : Real) * lower) ^ 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnleReal hT)
            (sq_nonneg _)
        _ = C2 / N := by
          dsimp [C2]
          field_simp [hNreal.ne', hlower.ne']
    · exact hupper
  simpa [sixVertexOddOffsetBoundaryError, r, lower, T] using hfirst.add hsecond

theorem tendsto_sixVertexOddOffsetSourceMoveError
    (c : Real) (s : Nat) :
    Tendsto (fun k => sixVertexOddOffsetSourceMoveError c s
      (sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) := by
  let r := 2 * s + 1
  let C := (r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) *
      sixVertexOddOffsetUniformBound c s
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  convert hzero using 1
  funext k
  dsimp [C, r]
  unfold sixVertexOddOffsetSourceMoveError
  push_cast
  ring

theorem tendsto_sixVertexOddOffsetNodalError_nonperiodic
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexOddOffsetNodalError c s
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
      (sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
        (sixVertexTailFiniteDensityFloor c) G D)) atTop (nhds 0) := by
  have hresidual := tendsto_sixVertexOddOffsetResidualError c s
  have hboundary := tendsto_sixVertexOddOffsetBoundaryError hc htail s
  have hsource := tendsto_sixVertexOddOffsetSourceMoveError c s
  have hlower := sixVertexTailFiniteDensityFloor_pos hc htail
  have htest := tendsto_sixVertexFixedChargeNonperiodicOffsetTestError c
    (2 * s + 1) hlower G D
  have htestScaled := htest.const_mul (2 * s + 1 : Real)
  simpa [sixVertexOddOffsetNodalError] using
    (((hresidual.add hboundary).add hsource).add htestScaled)

theorem tendsto_sixVertexOddOffsetNodalBound_nonperiodic
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k =>
      sixVertexOddOffsetNodalError c s
          (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
            (sixVertexTailFiniteDensityFloor c) G D) /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1))
      atTop (nhds 0) := by
  have herror := tendsto_sixVertexOddOffsetNodalError_nonperiodic
    hc htail s G D
  have hmargin := tendsto_sixVertexFixedChargeOffsetNetMargin
    hc htail (2 * s + 1)
  have hmarginPos := sixVertexFixedChargeOffsetContractionMargin_pos hc
  simpa using herror.div hmargin hmarginPos.ne'




theorem eventually_uniform_oddChargeDensityOffset_nonperiodic
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) *
            sixVertexOddChargeBetheOffset hc s k i -
          (2 * s + 1 : Real) *
            tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)| <
          epsilon := by
  have hbound := tendsto_sixVertexOddOffsetNodalBound_nonperiodic
    hc htail s G D
  have hsmall : ∀ᶠ k : Nat in atTop,
      sixVertexOddOffsetNodalError c s
          (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
            (sixVertexTailFiniteDensityFloor c) G D) /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) < epsilon :=
    hbound.eventually (Iio_mem_nhds hepsilon)
  filter_upwards
    [eventually_sixVertexFixedChargeOffsetNetMargin_pos hc htail (2 * s + 1),
      hsmall] with k hkmargin hksmall
  intro i
  have hN := sixVertexFourWidth_pos (2 * s + 1) k
  have hn := sixVertexFixedChargeBetheParticleCount_pos (2 * s + 1) k
  have hcharge : sixVertexFourWidth (2 * s + 1) k =
      2 * sixVertexFixedChargeBetheParticleCount (2 * s + 1) k +
        2 * (2 * s + 1) := by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  have hlower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hdensity : forall y,
      sixVertexTailFiniteDensityFloor c <=
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) y := by
    intro y
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s + 1) k)
      _ y
  have hquad (l : Fin
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
      hc hN hn hcharge
      (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k)
      (sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k)
      hlower hdensity
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)
      htauLip htauBound
  exact (abs_oddChargeDensityOffset_sub_continuous_le_tail_of_quadrature
    hc htail s k htauOdd htauEq hquad hkmargin i).trans_lt hksmall

end

end StatMech.FrontierD
