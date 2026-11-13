/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetFiniteResidual
import Code.FrontierD.SixVertexBetheContinuousOffset









namespace StatMech.FrontierD

open Finset

noncomputable section


theorem sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s) k)
            (sixVertexFixedChargeBetheRoots hc (2 * s) k)
            (sixVertexFixedChargeBetheRoots hc (2 * s) k j) *
          sixVertexEvenChargeBetheOffset hc s k j) -
        sixVertexEvenChargeOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k l) *
            sixVertexEvenChargeBetheOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s) k).ne'
  have hkernel (l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
      sixVertexContinuousOffsetKernel c (q j) (q l) =
        -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l) := by
    exact sixVertexContinuousOffsetKernel_eq_thetaRightDerivative hc _ _ |>.trans
      ((hasDerivAt_sixVertexTheta_right hc (q j) (q l)).deriv)
  unfold sixVertexEvenChargeOffsetNodalResidual
  change eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) q (q j) *
          eps j) -
      sixVertexEvenChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring


theorem sixVertexOddChargeOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
            (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) *
          sixVertexOddChargeBetheOffset hc s k j) -
        sixVertexOddChargeOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s + 1) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) *
            sixVertexOddChargeBetheOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let eps := sixVertexOddChargeBetheOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have hkernel
      (l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
      sixVertexContinuousOffsetKernel c (q j) (q l) =
        -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l) := by
    exact sixVertexContinuousOffsetKernel_eq_thetaRightDerivative hc _ _ |>.trans
      ((hasDerivAt_sixVertexTheta_right hc (q j) (q l)).deriv)
  unfold sixVertexOddChargeOffsetNodalResidual
  change eps j - sixVertexOddChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi *
        (sixVertexFiniteRootDensity c N
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) q (q j) *
          eps j) -
      sixVertexOddChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring

end

end StatMech.FrontierD
