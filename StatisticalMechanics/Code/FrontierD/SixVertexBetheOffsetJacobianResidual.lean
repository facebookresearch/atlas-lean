/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetFiniteResidual
import Code.FrontierD.SixVertexBetheOffsetSymmetry
import Code.FrontierD.SixVertexBetheSymmetricInverseBound










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator
    {N n : Nat} (hN : 0 < N) (c : Real) (q eps : Fin n -> Real)
    (j : Fin n) :
    (sixVertexBetheJacobianMatrix N n c q).mulVec eps j / N =
      eps j + (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) := by
  classical
  let A : Fin n -> Real := fun l =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
      sixVertexThetaDerivativeDenominator c (q j) (q l)
  let B : Fin n -> Real := fun l =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
      sixVertexThetaDerivativeDenominator c (q j) (q l)
  have hself : A j + B j = 0 := by
    dsimp [A, B]
    ring
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Matrix.mulVec, dotProduct]
  have hrow :
      (∑ k, sixVertexBetheJacobianMatrix N n c q j k * eps k) =
        ((N : Real) + ∑ l ∈ univ.erase j, A l) * eps j +
          ∑ l ∈ univ.erase j, B l * eps l := by
    rw [<- sum_erase_add _ _ (mem_univ j)]
    have hoff :
        (∑ l ∈ univ.erase j,
            sixVertexBetheJacobianMatrix N n c q j l * eps l) =
          ∑ l ∈ univ.erase j, B l * eps l := by
      apply sum_congr rfl
      intro l hl
      rw [sixVertexBetheJacobianMatrix,
        if_neg (Ne.symm (mem_erase.mp hl).1)]
    rw [sixVertexBetheJacobianMatrix, if_pos rfl, hoff]
    ring
  rw [hrow]
  have hsum :
      (∑ l, (A l * eps j + B l * eps l)) =
        (∑ l ∈ univ.erase j, A l) * eps j +
          ∑ l ∈ univ.erase j, B l * eps l := by
    calc
      (∑ l, (A l * eps j + B l * eps l)) =
          (∑ l ∈ univ.erase j, (A l * eps j + B l * eps l)) +
            (A j * eps j + B j * eps j) := by
              rw [sum_erase_add _ _ (mem_univ j)]
      _ = ∑ l ∈ univ.erase j, (A l * eps j + B l * eps l) := by
        rw [<- add_mul, hself, zero_mul, add_zero]
      _ = (∑ l ∈ univ.erase j, A l) * eps j +
          ∑ l ∈ univ.erase j, B l * eps l := by
        rw [sum_add_distrib, sum_mul]
  change (((N : Real) + ∑ l ∈ univ.erase j, A l) * eps j +
      ∑ l ∈ univ.erase j, B l * eps l) / N = _
  change _ = eps j + (1 / (N : Real)) *
    ∑ l, (A l * eps j + B l * eps l)
  rw [hsum]
  field_simp [hN0]
  ring


theorem sixVertexEvenChargeOffsetNodalResidual_eq_jacobian
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeOffsetNodalResidual hc s k j =
      (sixVertexBetheJacobianMatrix (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k) c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)).mulVec
          (sixVertexEvenChargeBetheOffset hc s k) j /
        sixVertexFourWidth (2 * s) k -
      sixVertexEvenChargeOffsetBoundarySource hc s k j := by
  let N := sixVertexFourWidth (2 * s) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  have hlinear :=
    sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator
      (sixVertexFourWidth_pos (2 * s) k) c q eps j
  change eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) = _
  change (sixVertexBetheJacobianMatrix N n c q).mulVec eps j / N =
      eps j + (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)
    at hlinear
  linarith


theorem sixVertexOddChargeOffsetNodalResidual_eq_jacobian
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeOffsetNodalResidual hc s k j =
      (sixVertexBetheJacobianMatrix (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)).mulVec
          (sixVertexOddChargeBetheOffset hc s k) j /
        sixVertexFourWidth (2 * s + 1) k -
      sixVertexOddChargeOffsetBoundarySource hc s k j := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s + 1) k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
  let eps := sixVertexOddChargeBetheOffset hc s k
  have hlinear :=
    sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator
      (sixVertexFourWidth_pos (2 * s + 1) k) c q eps j
  change eps j - sixVertexOddChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) = _
  change (sixVertexBetheJacobianMatrix N n c q).mulVec eps j / N =
      eps j + (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)
    at hlinear
  linarith

theorem sixVertexEvenChargeAlignedHalfRoots_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeAlignedHalfRoots hc s k j.rev =
      -sixVertexEvenChargeAlignedHalfRoots hc s k j := by
  have hindex : sixVertexEvenChargeHalfIndex s k j.rev =
      (sixVertexEvenChargeHalfIndex s k j).rev := by
    apply Fin.ext
    simp only [sixVertexEvenChargeHalfIndex, Fin.rev, Fin.val_mk]
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
    omega
  unfold sixVertexEvenChargeAlignedHalfRoots
  rw [hindex]
  exact (sixVertexHalfFilledBetheRoots_mem_open hc (2 * s + k)).2.1
    (sixVertexEvenChargeHalfIndex s k j)

end

end StatMech.FrontierD
