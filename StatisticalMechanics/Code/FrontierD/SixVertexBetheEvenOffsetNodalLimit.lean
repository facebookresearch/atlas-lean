/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetBoundaryEstimate
import Code.FrontierD.SixVertexBetheOffsetDiscreteStability
import Code.FrontierD.SixVertexBetheOffsetRowContraction
import Code.FrontierD.SixVertexBetheOffsetTestQuadrature
import Code.FrontierD.SixVertexBetheEvenRootOffsetBound










namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexEvenOffsetUniformBound (c : Real) (s : Nat) : Real :=
  Real.pi *
      (sixVertexFixedChargeDensityInvWidthConstant c 0 +
        sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) /
    (((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) *
      sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetResidualError
    (c : Real) (s N : Nat) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexEvenOffsetUniformBound c s ^ 2 / N

def sixVertexEvenOffsetBoundaryError
    (c : Real) (s N : Nat) : Real :=
  2 * (s : Real) ^ 2 *
      (sixVertexThetaRightLipschitzNNReal c : Real) /
    ((N : Real) * sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetSourceMoveError
    (c : Real) (s N : Nat) : Real :=
  (2 * s : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
    (sixVertexEvenOffsetUniformBound c s / N)

def sixVertexFixedChargeOffsetNetMargin
    (c : Real) (N r : Nat) : Real :=
  sixVertexRootDensityKernelFloor c *
      (sixVertexRootDensityScale c /
        (4 * (sixVertexAnisotropyMagnitude c + 1) *
          sixVertexFiniteRootDensityUniformBound c)) -
    sixVertexFixedChargeOffsetRowError c N r
      (sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetNodalError
    (c : Real) (s N : Nat) (G : Real) (D : NNReal) : Real :=
  sixVertexEvenOffsetResidualError c s N +
    sixVertexEvenOffsetBoundaryError c s N +
    sixVertexEvenOffsetSourceMoveError c s N +
    (2 * s : Real) * sixVertexFixedChargeOffsetTestError c N (2 * s)
      (sixVertexTailFiniteDensityFloor c) G D



theorem abs_evenChargeDensityOffset_sub_continuous_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauPeriodic : Function.Periodic tau (2 * Real.pi))
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c
      (sixVertexFourWidth (2 * s) k) (2 * s))
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j) *
        sixVertexEvenChargeBetheOffset hc s k j -
      (2 * s : Real) *
        tau (sixVertexFixedChargeBetheRoots hc (2 * s) k j)| <=
      sixVertexEvenOffsetNodalError c s
          (sixVertexFourWidth (2 * s) k) G D /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s) := by
  let N := sixVertexFourWidth (2 * s) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s) k
  let p := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let rhoF := sixVertexFiniteRootDensity c N n p
  let eps := sixVertexEvenChargeBetheOffset hc s k
  let a : Real := 2 * s
  let e : Fin n -> Real := fun l => rhoF (p l) * eps l - a * tau (p l)
  let lower := sixVertexTailFiniteDensityFloor c
  let reciprocalMass := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  let rowError := sixVertexFixedChargeOffsetRowError c N (2 * s) lower
  let rowBound := 2 * Real.pi + rowError
  let residualError := sixVertexEvenOffsetResidualError c s N
  let boundaryError := sixVertexEvenOffsetBoundaryError c s N
  let testError := sixVertexFixedChargeOffsetTestError c N (2 * s) lower G D
  let sourceMoveError := sixVertexEvenOffsetSourceMoveError c s N
  let eta := residualError + boundaryError + sourceMoveError + a * testError
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : 0 < n := sixVertexFixedChargeBetheParticleCount_pos (2 * s) k
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hdensity : forall y, lower <= rhoF y := by
    intro y
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) p y
  have hrho (l : Fin n) : 0 < rhoF (p l) := hlower.trans_le (hdensity _)
  have hmass : (1 / (N : Real)) * ∑ l,
      e l / (sixVertexRootDensityWeight c (p l) * rhoF (p l)) = 0 := by
    have hzero := sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero
      hc s k htauOdd a
    change ∑ l, e l /
      (sixVertexRootDensityWeight c (p l) * rhoF (p l)) = 0 at hzero
    rw [hzero, mul_zero]
  have hrow (i : Fin n) : (1 / (N : Real)) * ∑ l,
      sixVertexContinuousOffsetKernel c (p i) (p l) / rhoF (p l) <=
        rowBound := by
    exact empiricalContinuousOffsetKernel_fixedCharge_le
      hc htail (2 * s) k i
  have hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ l,
      1 / (sixVertexRootDensityWeight c (p l) * rhoF (p l)) := by
    exact reciprocalWeightDensityMass_fixedCharge_le hc htail (2 * s) k
  have hB : 0 <= sixVertexEvenOffsetUniformBound c s := by
    unfold sixVertexEvenOffsetUniformBound
    have hE0 := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail 0
    have hEr := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail (2 * s)
    have hwmin : 0 < (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c := div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
    positivity
  have hoffset (l : Fin n) : |eps l| <= sixVertexEvenOffsetUniformBound c s := by
    exact abs_sixVertexEvenChargeBetheOffset_le_tail hc htail s k l
  have hresidual (i : Fin n) :
      |sixVertexEvenChargeOffsetNodalResidual hc s k i| <= residualError := by
    exact abs_sixVertexEvenChargeOffsetNodalResidual_le
      hc s k hB hoffset i
  have hhalfDensity : forall y,
      lower <= sixVertexFiniteRootDensity c
        (sixVertexFourWidth 0 (2 * s + k))
        ((2 * s + k + 1) + (2 * s + k + 1))
        (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y := by
    intro y
    apply sixVertexTailFiniteDensityFloor_le hc
      (sixVertexFourWidth_pos 0 (2 * s + k))
    · unfold sixVertexFourWidth
      omega
  have hboundary (i : Fin n) :
      |sixVertexEvenChargeOffsetBoundarySource hc s k i -
        a * sixVertexContinuousOffsetSource c
          (sixVertexEvenChargeAlignedHalfRoots hc s k i)| <= boundaryError := by
    have h := abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le
      hc s k hlower hhalfDensity i
    have hwidth : sixVertexFourWidth 0 (2 * s + k) = N := by
      dsimp [N]
      unfold sixVertexFourWidth
      omega
    rw [hwidth] at h
    simpa [a, lower, boundaryError, sixVertexEvenOffsetBoundaryError] using h
  have hcharge : N = 2 * n + 2 * (2 * s) := by
    dsimp [N, n]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  have hquad (i : Fin n) :
      |(∑ l, sixVertexContinuousOffsetKernel c (p i) (p l) * tau (p l) /
          rhoF (p l)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c (p i) y * tau y| <= testError := by
    exact abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz
      hc hN hn hcharge (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k)
      (sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k)
      hlower hdensity (p i) htauLip htauPeriodic htauBound
  have hdefect (i : Fin n) :
      |2 * Real.pi * e i + (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (p i) (p l) / rhoF (p l) * e l| <=
          eta := by
    let empiricalTau :=
      (∑ l, sixVertexContinuousOffsetKernel c (p i) (p l) * tau (p l) /
        rhoF (p l)) / (N : Real)
    let integralTau := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c (p i) y * tau y
    have hqIcc : p i ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨((sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.2 i).1.le,
        ((sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.2 i).2.le⟩
    have htau := htauEq (p i) hqIcc
    have hres := sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution
      hc s k i
    have hsourcePoint :
        sixVertexEvenChargeAlignedHalfRoots hc s k i =
          p i - eps i / N := by
      dsimp [eps]
      unfold sixVertexEvenChargeBetheOffset
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      change _ = p i - ((N : Real) * (p i - _)) / N
      field_simp [hN0]
      ring
      rfl
    have hsourceMove :
        |a * (sixVertexContinuousOffsetSource c
              (sixVertexEvenChargeAlignedHalfRoots hc s k i) -
            sixVertexContinuousOffsetSource c (p i))| <=
          a * (sixVertexThetaRightLipschitzNNReal c : Real) *
            (sixVertexEvenOffsetUniformBound c s / N) := by
      have hsourceLip : LipschitzWith (sixVertexThetaRightLipschitzNNReal c)
          (sixVertexContinuousOffsetSource c) := by
        apply LipschitzWith.of_dist_le_mul
        intro x z
        unfold sixVertexContinuousOffsetSource
        rw [Real.dist_eq, Real.dist_eq]
        have hleft := (lipschitzWith_sixVertexTheta_right hc (-Real.pi)).dist_le_mul x z
        have hright := (lipschitzWith_sixVertexTheta_right hc Real.pi).dist_le_mul x z
        rw [Real.dist_eq, Real.dist_eq] at hleft hright
        have hleft' :
            |sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| <=
              (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by
          calc
            |sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| =
                |-(sixVertexTheta c x (-Real.pi) -
                  sixVertexTheta c z (-Real.pi))| := (abs_neg _).symm
            _ = |sixVertexTheta c (-Real.pi) x -
                sixVertexTheta c (-Real.pi) z| := by
                  congr 1
                  rw [neg_sub, sixVertexTheta_antisymm c x (-Real.pi),
                    sixVertexTheta_antisymm c z (-Real.pi)]
                  ring
            _ <= _ := hleft
        have hright' :
            |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi| <=
              (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by
          calc
            |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi| =
                |-(sixVertexTheta c x Real.pi -
                  sixVertexTheta c z Real.pi)| := (abs_neg _).symm
            _ = |sixVertexTheta c Real.pi x -
                sixVertexTheta c Real.pi z| := by
                  congr 1
                  rw [neg_sub, sixVertexTheta_antisymm c x Real.pi,
                    sixVertexTheta_antisymm c z Real.pi]
                  ring
            _ <= _ := hright
        calc
          |(sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2 -
              (sixVertexTheta c z (-Real.pi) + sixVertexTheta c z Real.pi) / 2| <=
              (|sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| +
                |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi|) / 2 := by
                rw [show (sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2 -
                    (sixVertexTheta c z (-Real.pi) + sixVertexTheta c z Real.pi) / 2 =
                  ((sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)) +
                    (sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi)) / 2 by ring,
                  abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
                gcongr
                exact abs_add_le _ _
          _ <= ((sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| +
              (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z|) / 2 := by
                gcongr
          _ = (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by ring
      have hmove := hsourceLip.dist_le_mul
        (sixVertexEvenChargeAlignedHalfRoots hc s k i) (p i)
      rw [Real.dist_eq, Real.dist_eq, hsourcePoint] at hmove
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hepsN : |eps i / (N : Real)| <=
          sixVertexEvenOffsetUniformBound c s / N := by
        rw [abs_div, abs_of_pos hNreal]
        exact div_le_div_of_nonneg_right (hoffset i) hNreal.le
      have ha : 0 <= a := by positivity
      rw [abs_mul, abs_of_nonneg ha, hsourcePoint]
      have hmove' := hmove.trans
        (mul_le_mul_of_nonneg_left (by simpa using hepsN) (NNReal.coe_nonneg _))
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmove' ha
    have hidentity :
        2 * Real.pi * e i + (1 / (N : Real)) * ∑ l,
            sixVertexContinuousOffsetKernel c (p i) (p l) / rhoF (p l) * e l =
          sixVertexEvenChargeOffsetNodalResidual hc s k i +
            (sixVertexEvenChargeOffsetBoundarySource hc s k i -
              a * sixVertexContinuousOffsetSource c
                (sixVertexEvenChargeAlignedHalfRoots hc s k i)) +
            a * (sixVertexContinuousOffsetSource c
                (sixVertexEvenChargeAlignedHalfRoots hc s k i) -
              sixVertexContinuousOffsetSource c (p i)) +
            a * (integralTau - empiricalTau) := by
      change 2 * Real.pi * (rhoF (p i) * eps i - a * tau (p i)) + _ = _
      change sixVertexEvenChargeOffsetNodalResidual hc s k i =
          2 * Real.pi * (rhoF (p i) * eps i) -
            sixVertexEvenChargeOffsetBoundarySource hc s k i +
            (1 / (N : Real)) * ∑ l,
              sixVertexContinuousOffsetKernel c (p i) (p l) * eps l at hres
      change 2 * Real.pi * tau (p i) =
        sixVertexContinuousOffsetSource c (p i) - integralTau at htau
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      have hempirical :
          (1 / (N : Real)) * ∑ l,
              sixVertexContinuousOffsetKernel c (p i) (p l) / rhoF (p l) *
                (rhoF (p l) * eps l - a * tau (p l)) =
            (1 / (N : Real)) * ∑ l,
                sixVertexContinuousOffsetKernel c (p i) (p l) * eps l -
              a * empiricalTau := by
        dsimp [empiricalTau]
        field_simp [hN0]
        calc
          ∑ l,
              sixVertexContinuousOffsetKernel c (p i) (p l) *
                  (rhoF (p l) * eps l - a * tau (p l)) / rhoF (p l) =
              ∑ l, (sixVertexContinuousOffsetKernel c (p i) (p l) * eps l -
                a * (sixVertexContinuousOffsetKernel c (p i) (p l) *
                  tau (p l) / rhoF (p l))) := by
                    apply Finset.sum_congr rfl
                    intro l _
                    field_simp [(hrho l).ne']
          _ = (∑ l, sixVertexContinuousOffsetKernel c (p i) (p l) * eps l) -
              ∑ l, a * (sixVertexContinuousOffsetKernel c (p i) (p l) *
                tau (p l) / rhoF (p l)) := by rw [Finset.sum_sub_distrib]
          _ = (∑ l, sixVertexContinuousOffsetKernel c (p i) (p l) * eps l) -
              a * ∑ l, (sixVertexContinuousOffsetKernel c (p i) (p l) *
                tau (p l) / rhoF (p l)) := by rw [Finset.mul_sum]
      have hresRearrange :
          2 * Real.pi * (rhoF (p i) * eps i) +
              (1 / (N : Real)) * ∑ l,
                sixVertexContinuousOffsetKernel c (p i) (p l) * eps l =
            sixVertexEvenChargeOffsetNodalResidual hc s k i +
              sixVertexEvenChargeOffsetBoundarySource hc s k i := by
        linarith [hres]
      have htauScaled :
          2 * Real.pi * (a * tau (p i)) =
            a * sixVertexContinuousOffsetSource c (p i) - a * integralTau := by
        calc
          2 * Real.pi * (a * tau (p i)) = a * (2 * Real.pi * tau (p i)) := by ring
          _ = _ := by rw [htau]; ring
      change 2 * Real.pi * (rhoF (p i) * eps i - a * tau (p i)) + _ = _
      rw [hempirical]
      calc
        2 * Real.pi * (rhoF (p i) * eps i - a * tau (p i)) +
            ((1 / (N : Real)) * ∑ l,
              sixVertexContinuousOffsetKernel c (p i) (p l) * eps l -
              a * empiricalTau) =
            (2 * Real.pi * (rhoF (p i) * eps i) +
              (1 / (N : Real)) * ∑ l,
                sixVertexContinuousOffsetKernel c (p i) (p l) * eps l) -
              2 * Real.pi * (a * tau (p i)) - a * empiricalTau := by ring
        _ = (sixVertexEvenChargeOffsetNodalResidual hc s k i +
              sixVertexEvenChargeOffsetBoundarySource hc s k i) -
            (a * sixVertexContinuousOffsetSource c (p i) - a * integralTau) -
            a * empiricalTau := by rw [hresRearrange, htauScaled]
        _ = _ := by ring
    rw [hidentity]
    have hfour (A B C F : Real) :
        |A + B + C + F| <= |A| + |B| + |C| + |F| := by
      calc
        |A + B + C + F| <= |A + B + C| + |F| := abs_add_le _ _
        _ <= (|A + B| + |C|) + |F| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ <= ((|A| + |B|) + |C|) + |F| :=
          add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    calc
      |_ + _ + _ + _| <=
          |sixVertexEvenChargeOffsetNodalResidual hc s k i| +
          |sixVertexEvenChargeOffsetBoundarySource hc s k i -
            a * sixVertexContinuousOffsetSource c
              (sixVertexEvenChargeAlignedHalfRoots hc s k i)| +
          |a * (sixVertexContinuousOffsetSource c
                (sixVertexEvenChargeAlignedHalfRoots hc s k i) -
              sixVertexContinuousOffsetSource c (p i))| +
          |a * (integralTau - empiricalTau)| := hfour _ _ _ _
      _ <= residualError + boundaryError +
          a * (sixVertexThetaRightLipschitzNNReal c : Real) *
              (sixVertexEvenOffsetUniformBound c s / N) +
          a * testError := by
        apply add_le_add
        · exact add_le_add (add_le_add (hresidual i) (hboundary i)) hsourceMove
        · rw [abs_mul, abs_of_nonneg (by positivity : 0 <= a), abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hquad i) (by positivity)
      _ = eta := by
        dsimp [eta, residualError, boundaryError, sourceMoveError,
          testError, a, sixVertexEvenOffsetSourceMoveError]
  have hstable := discreteOffsetError_le_of_zeroMass hc hN hn hrho hmass hrow
    hreciprocal hdefect
  have hmargin' : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) := by
    have heq :
        2 * Real.pi -
            (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
          sixVertexFixedChargeOffsetNetMargin c N (2 * s) := by
      dsimp [rowBound, rowError, reciprocalMass,
        sixVertexFixedChargeOffsetNetMargin]
      ring
    rw [heq]
    exact hmargin
  have h := hstable hmargin' j
  have heq :
      2 * Real.pi -
          (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
        sixVertexFixedChargeOffsetNetMargin c N (2 * s) := by
    dsimp [rowBound, rowError, reciprocalMass,
      sixVertexFixedChargeOffsetNetMargin]
    ring
  rw [heq] at h
  simpa [e, eta, sixVertexEvenOffsetNodalError,
    rowBound, rowError,
    reciprocalMass, residualError, boundaryError, sourceMoveError, testError,
    lower, N, n, p, rhoF, eps, a] using h

end

end StatMech.FrontierD
