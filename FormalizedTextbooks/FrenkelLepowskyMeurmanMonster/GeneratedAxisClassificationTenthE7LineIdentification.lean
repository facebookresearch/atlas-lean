/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7MatrixPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisIntegralLineGeometry

/-! Identify the genuine unsigned norm-twelve line, retaining both orientations after transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice vector on the transported norm-twelve line. -/
def generatedTenthE7NormTwelveLine : leechIntegral :=
  ⟨generatedTenthE7DistinguishedVector, generatedTenth_e7_distinguished_mem⟩

private theorem original_line_ne_zero : generatedTenthNormTwelveLine ≠ 0 := by
  intro h
  have hn := generatedTenth_norm_twelve_square_sum
  change leechSquareSum generatedTenthNormTwelveLine.val = 96 at hn
  rw [h] at hn
  norm_num [leechSquareSum] at hn

/-- The original rank-one flag is precisely the physical projection onto the norm-twelve line. -/
theorem generatedTenth_norm_twelve_projection_line :
    generatedTenthLineProjection =
      (1 / 12 : ℝ) • generatedIntegralLineMatrix generatedTenthNormTwelveLine := by
  ext i j
  rw [Matrix.smul_apply, generatedIntegralLineMatrix_four_coordinates
    generatedTenthNormTwelveLine generatedTenthLineDirection (fun _ => rfl)]
  simp only [generatedTenthLineProjection, generatedTenthLineProjectionInteger,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  change (1 / 6 : ℝ) * ((generatedTenthLineDirection i *
    generatedTenthLineDirection j : ℤ) : ℝ) = _
  push_cast
  ring

/-- Every original actual matrix fixer preserves both orientations of the norm-twelve line. -/
theorem generatedTenth_matrix_fixer_norm_twelve_line (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1) :
    leechIntegralAction g generatedTenthNormTwelveLine = generatedTenthNormTwelveLine ∨
      leechIntegralAction g generatedTenthNormTwelveLine = -generatedTenthNormTwelveLine := by
  have hline := ((generatedTenth_matrix_fix_flag_iff g).mp hg).2
  rw [generatedTenth_norm_twelve_projection_line] at hline
  exact (generatedIntegralLineMatrix_smul_fix_iff g _ original_line_ne_zero _
    (by norm_num)).mp hline

/-- The full actual integral norm-twelve vector is transported with its displayed orientation. -/
theorem generatedTenth_e7_norm_twelve_transport :
    leechIntegralAction generatedTenthE7Isometry generatedTenthNormTwelveLine =
      generatedTenthE7NormTwelveLine := by
  have hi : generatedTenthE7Numerator *ᵥ generatedTenthNormTwelveVector =
      (2 : ℤ) • generatedTenthE7DistinguishedVector := by
    change generatedTenthE7Numerator *ᵥ ((4 : ℤ) • generatedTenthLineDirection) =
      (2 : ℤ) • ((4 : ℤ) • generatedTenthE7LineDirection)
    rw [Matrix.mulVec_smul, generatedTenth_e7_line_direction_integer, smul_smul,
      smul_smul]
    norm_num
  have hr : generatedTenthE7Numerator.map (Int.castRingHom ℝ) *ᵥ
      (fun i => (generatedTenthNormTwelveVector i : ℝ)) =
        (2 : ℝ) • (fun i => (generatedTenthE7DistinguishedVector i : ℝ)) := by
    ext i
    have hh := congrArg (Int.castRingHom ℝ) (congrFun hi i)
    change ((∑ k, generatedTenthE7Numerator i k *
      generatedTenthNormTwelveVector k : ℤ) : ℝ) =
        ((2 * generatedTenthE7DistinguishedVector i : ℤ) : ℝ) at hh
    push_cast at hh
    exact hh
  have he (v : Fin 24 → ℤ) : leechCoordinateEmbedding v =
      (Real.sqrt 8)⁻¹ • (fun i => (v i : ℝ)) := by
    ext i
    change (v i : ℝ) / Real.sqrt 8 = (Real.sqrt 8)⁻¹ * (v i : ℝ)
    ring
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding, generatedTenth_e7_isometry_apply]
  change generatedTenthE7Matrix *ᵥ leechCoordinateEmbedding generatedTenthNormTwelveVector =
    leechCoordinateEmbedding generatedTenthE7DistinguishedVector
  rw [he, he]
  simp only [generatedTenthE7Matrix, generatedTwelfthCertifiedRealMatrix,
    Matrix.smul_mulVec, Matrix.mulVec_smul, hr, smul_smul]
  norm_num

/-- Both unsigned orientations of the actual transported norm-twelve line remain explicit. -/
theorem generatedTenth_e7_matrix_fixer_norm_twelve_line (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1) :
    leechIntegralAction (generatedTenthE7TransportedSpatial g) generatedTenthE7NormTwelveLine =
        generatedTenthE7NormTwelveLine ∨
      leechIntegralAction (generatedTenthE7TransportedSpatial g) generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine := by
  have ht := generatedTenth_e7_norm_twelve_transport
  have hinv : leechIntegralAction generatedTenthE7Isometry⁻¹
      generatedTenthE7NormTwelveLine = generatedTenthNormTwelveLine := by
    rw [← ht, map_inv]
    exact (leechIntegralAction generatedTenthE7Isometry).symm_apply_apply _
  rcases generatedTenth_matrix_fixer_norm_twelve_line g hg with h | h
  · left
    change leechIntegralAction
      (generatedTenthE7Isometry * g * generatedTenthE7Isometry⁻¹) _ = _
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, h, ht]
  · right
    change leechIntegralAction
      (generatedTenthE7Isometry * g * generatedTenthE7Isometry⁻¹) _ = _
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, h, map_neg, ht]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
