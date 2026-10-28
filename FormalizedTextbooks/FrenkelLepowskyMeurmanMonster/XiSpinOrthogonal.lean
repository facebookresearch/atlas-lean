/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonality and invertibility of the explicit source Gauss operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinOrthogonalLift

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- Orthogonal extraspecial operators have the expected adjoints. -/
theorem xiSpinOperator_pairing_adjoint (q : Q) (f h : SpinSpace) :
    spinPairing (spinOperator q f) h = spinPairing f (spinOperator q⁻¹ h) := by
  have hh := spinRepresentation_pairing q f (spinRepresentation q⁻¹ h)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    show (1 : SpinSpace ≃ₗ[ℝ] SpinSpace) h = h from rfl] at hh
  exact hh

theorem xiSpinPairing_sum_left {ι : Type*} [Fintype ι] (f : ι → SpinSpace) (h : SpinSpace) :
    spinPairing (∑ i, f i) h = ∑ i, spinPairing (f i) h := by
  simp only [spinPairing, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem xiSpinPairing_sum_right {ι : Type*} [Fintype ι] (f : SpinSpace) (h : ι → SpinSpace) :
    spinPairing f (∑ i, h i) = ∑ i, spinPairing f (h i) := by
  simp only [spinPairing, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Every grey group representation consists of actual involutions. -/
theorem xiGrayHom_inverse (F : Multiplicative XiGrayIndex →* Q) (a : XiGrayIndex) :
    (F (ofAdd a))⁻¹ = F (ofAdd a) := by
  rw [← map_inv]
  congr 1
  apply toAdd.injective
  change -a = a
  ext i
  exact CharTwo.neg_eq _

/-- The two source Gaussian sums are self-adjoint, term by term. -/
theorem xiGrayGaussian_spin_adjoint (F : Multiplicative XiGrayIndex →* Q) (f h : SpinSpace) :
    spinPairing (xiGrayGaussian (spinLinearRepresentation.comp F) f) h =
      spinPairing f (xiGrayGaussian (spinLinearRepresentation.comp F) h) := by
  classical
  unfold xiGrayGaussian
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, MonoidHom.comp_apply]
  simp_rw [spinPairing_smul_left, spinPairing_smul_right, xiSpinPairing_sum_left,
    xiSpinPairing_sum_right, spinPairing_smul_left, spinPairing_smul_right]
  congr 2
  ext a
  change qSign (xiGrayQuadratic a) * spinPairing (spinOperator (F (ofAdd a)) f) h =
    qSign (xiGrayQuadratic a) * spinPairing f (spinOperator (F (ofAdd a)) h)
  rw [xiSpinOperator_pairing_adjoint, xiGrayHom_inverse]

set_option maxRecDepth 4096 in
/-- Self-adjoint Gaussian involutions preserve the actual Euclidean pairing. -/
theorem xiGrayGaussian_spin_pairing (F : Multiplicative XiGrayIndex →* Q) (f h : SpinSpace) :
    spinPairing (xiGrayGaussian (spinLinearRepresentation.comp F) f)
      (xiGrayGaussian (spinLinearRepresentation.comp F) h) = spinPairing f h := by
  rw [xiGrayGaussian_spin_adjoint]
  have heq : xiGrayGaussian (spinLinearRepresentation.comp F)
      (xiGrayGaussian (spinLinearRepresentation.comp F) h) = h :=
    congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T h) (xiGrayGaussian_square _)
  rw [heq]

set_option maxRecDepth 4096 in
/-- The first Gaussian involution as its explicitly self-inverse linear equivalence. -/
noncomputable def xiSpinGammaEquiv : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  LinearEquiv.ofInvolutive xiSpinGamma (fun f =>
    congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) xiSpinGamma_square)

set_option maxRecDepth 4096 in
/-- The second Gaussian involution as its explicitly self-inverse linear equivalence. -/
noncomputable def xiSpinGEquiv : SpinSpace ≃ₗ[ℝ] SpinSpace :=
  LinearEquiv.ofInvolutive xiSpinG (fun f =>
    congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) xiSpinG_square)

/-- The first equivalence retains the explicitly constructed Gaussian operator. -/
@[simp] theorem xiSpinGammaEquiv_toLinearMap : xiSpinGammaEquiv.toLinearMap = xiSpinGamma := rfl

/-- The second equivalence retains the explicitly constructed Gaussian operator. -/
@[simp] theorem xiSpinGEquiv_toLinearMap : xiSpinGEquiv.toLinearMap = xiSpinG := rfl

/-- The column operator for source ξ=ξ_γ ξ_g. -/
noncomputable def xiSpinEquiv : SpinSpace ≃ₗ[ℝ] SpinSpace := xiSpinGEquiv * xiSpinGammaEquiv

set_option maxRecDepth 4096 in
theorem xiSpinGamma_pairing (f h : SpinSpace) :
    spinPairing (xiSpinGamma f) (xiSpinGamma h) = spinPairing f h :=
  xiGrayGaussian_spin_pairing _ _ _

set_option maxRecDepth 4096 in
theorem xiSpinG_pairing (f h : SpinSpace) :
    spinPairing (xiSpinG f) (xiSpinG h) = spinPairing f h :=
  xiGrayGaussian_spin_pairing _ _ _

set_option maxRecDepth 4096 in
theorem xiSpinEquiv_pairing (f h : SpinSpace) :
    spinPairing (xiSpinEquiv f) (xiSpinEquiv h) = spinPairing f h := by
  change spinPairing (xiSpinG (xiSpinGamma f)) (xiSpinG (xiSpinGamma h)) = _
  rw [xiSpinG_pairing, xiSpinGamma_pairing]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
