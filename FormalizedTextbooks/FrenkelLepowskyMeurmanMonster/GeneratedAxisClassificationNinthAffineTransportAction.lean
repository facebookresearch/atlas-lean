/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineTransportNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Original integral basis-action certificates bind the complete genuine lattice transport
to its binary matrix. The modular action is derived from the actual lattice isometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem xi_real_numerator : co1XiMatrix =
    (1 / 2 : ℝ) • co1XiNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change (((co1XiNumerator i j : ℚ) / 2 : ℚ) : ℝ) =
    (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
  push_cast
  ring

/-- The complete actual physical column action has the certified original integer numerator. -/
theorem generatedNinth_affine_transport_apply (u : Fin 24 → ℝ) :
    generatedNinthAffineTransport.val u =
      (1 / 2 : ℝ) •
        (generatedNinthAffineTransportNumerator.map (Int.castRingHom ℝ) *ᵥ u) := by
  change golayRealPermute generatedNinthAffineOctadPermutation.val
      (co1XiEquiv.symm
        (golayRealPermute generatedNinthSectionPermutation.val
          (golayRealSign generatedNinthSectionSign.val u))) = _
  rw [co1XiEquiv_symm_apply, co1XiMatrix_square_eq_transpose, xi_real_numerator]
  ext i
  change (((1 / 2 : ℝ) • co1XiNumerator.map (Int.castRingHom ℝ)).transpose *ᵥ
      golayRealPermute generatedNinthSectionPermutation.val
        (golayRealSign generatedNinthSectionSign.val u))
        (generatedNinthAffineOctadPermutation.val.symm i) = _
  simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (∑ k : Fin 24, (co1XiNumerator k
      (generatedNinthAffineOctadPermutation.val.symm i) : ℝ) *
        golayRealPermute generatedNinthSectionPermutation.val
          (golayRealSign generatedNinthSectionSign.val u) k) =
    ∑ j : Fin 24, (generatedNinthAffineTransportNumerator i j : ℝ) * u j
  rw [← Equiv.sum_comp generatedNinthSectionPermutation.val]
  simp only [golayRealPermute_apply, golayRealSign_apply, Equiv.symm_apply_apply]
  rw [(generatedNinth_affine_octad_permutation_coordinates i).2]
  apply Finset.sum_congr rfl
  intro j _
  rw [(generatedNinth_section_permutation_coordinates j).1]
  by_cases h : generatedNinthSectionSign.val j = 0 <;>
    simp [generatedNinthAffineTransportNumerator, qSign, h]

/-- The verified integer matrix acts on every vector in the actual original Leech basis. -/
theorem generatedNinth_affine_transport_basis_action (z : Fin 24 → ℤ) :
    generatedNinthAffineTransport.val
        (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding
        (leechBasisMatrix *ᵥ (generatedNinthAffineTransportBasisMatrix *ᵥ z)) := by
  have hv := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℤ => A *ᵥ z)
    generatedNinth_affine_transport_integral_certificate
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec] at hv
  rw [generatedNinth_affine_transport_apply]
  ext i
  have hi : (∑ j : Fin 24, (generatedNinthAffineTransportNumerator i j : ℝ) *
      ((leechBasisMatrix *ᵥ z) j : ℝ)) =
    2 * ((leechBasisMatrix *ᵥ
      (generatedNinthAffineTransportBasisMatrix *ᵥ z)) i : ℝ) := by
    exact_mod_cast congrFun hv i
  change (1 / 2 : ℝ) *
      (∑ j : Fin 24, (generatedNinthAffineTransportNumerator i j : ℝ) *
        (((leechBasisMatrix *ᵥ z) j : ℝ) / Real.sqrt 8)) =
    ((leechBasisMatrix *ᵥ
      (generatedNinthAffineTransportBasisMatrix *ᵥ z)) i : ℝ) / Real.sqrt 8
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, hi]
  ring

/-- Every original binary vector has the action derived from the genuine lattice transport. -/
theorem generatedNinth_affine_transport_binary_action (v : Fin 24 → ZMod 2) :
    leechBinaryAction generatedNinthAffineTransport v =
      sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ v := by
  rw [leechBinaryAction_of_basis_certificate generatedNinthAffineTransport
    generatedNinthAffineTransportBasisMatrix generatedNinth_affine_transport_basis_action]
  rw [generatedNinth_affine_transport_binary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
