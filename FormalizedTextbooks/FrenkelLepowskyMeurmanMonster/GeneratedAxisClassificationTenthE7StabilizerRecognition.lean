/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7LineIdentification

/-! Exact original matrix-stabilizer recognition by the transported E7 space
and unsigned norm-twelve line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem transport_product (g : leechIsomSubgroup) :
    generatedTenthE7TransportedSpatial g * generatedTenthE7Isometry =
      generatedTenthE7Isometry * g := by
  simp [generatedTenthE7TransportedSpatial, mul_assoc]

private theorem pair_projection_transport :
    conwayMatrixAction generatedTenthE7Isometry generatedTenthPairProjection =
      (1 / 2 : ℝ) • generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) := by
  have hm : leechIsomMatrix generatedTenthE7Isometry = generatedTenthE7Matrix := by
    ext i j
    change generatedTenthE7Isometry.val (Pi.single j 1) i = generatedTenthE7Matrix i j
    rw [generatedTenth_e7_isometry_apply, Matrix.mulVec_single_one]
    rfl
  rw [conwayMatrixAction_eq_conjugate, hm, generatedTenthPairProjection,
    Matrix.mul_smul, Matrix.smul_mul, generatedTenth_e7_pair_projection_real]

private theorem matrix_fixed_of_commute (e : leechIsomSubgroup)
    (A : Matrix (Fin 24) (Fin 24) ℝ)
    (he : ∀ x, e.val (A *ᵥ x) = A *ᵥ e.val x) : conwayMatrixAction e A = A := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := e.val.surjective x
  change conwayMatrixAction e A *ᵥ e.val y = A *ᵥ e.val y
  rw [conwayMatrixAction_mulVec]
  exact he y

private theorem original_line_ne_zero : generatedTenthNormTwelveLine ≠ 0 := by
  intro h
  have hn := generatedTenth_norm_twelve_square_sum
  change leechSquareSum generatedTenthNormTwelveLine.val = 96 at hn
  rw [h] at hn
  norm_num [leechSquareSum] at hn

/-- The original actual matrix stabilizer is exactly the transported E7 stabilizer
intersected with the actual unsigned norm-twelve line stabilizer. -/
theorem generatedTenth_e7_matrix_stabilizer_recognition (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
        (griessConwayEncode generatedTenthAxis).1 ↔
      (∀ x : Fin 24 → ℝ,
        generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
          generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
              (generatedTenthE7TransportedSpatial g).val x =
            (2 : ℝ) • (generatedTenthE7TransportedSpatial g).val x) ∧
      (leechIntegralAction (generatedTenthE7TransportedSpatial g)
          generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
        leechIntegralAction (generatedTenthE7TransportedSpatial g)
          generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine) := by
  constructor
  · intro hg
    exact ⟨generatedTenth_e7_matrix_fixer_eigenspace g hg,
      generatedTenth_e7_matrix_fixer_norm_twelve_line g hg⟩
  · rintro ⟨hspace, hline⟩
    have hprojection := matrix_fixed_of_commute (generatedTenthE7TransportedSpatial g)
      (generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ))
      (generatedTenth_e7_projection_commute_of_eigenspace _ hspace)
    have hpair : conwayMatrixAction g generatedTenthPairProjection =
        generatedTenthPairProjection := by
      apply (conwayMatrixAction generatedTenthE7Isometry).injective
      have hc : conwayMatrixAction (generatedTenthE7TransportedSpatial g)
          (conwayMatrixAction generatedTenthE7Isometry generatedTenthPairProjection) =
          conwayMatrixAction generatedTenthE7Isometry
            (conwayMatrixAction g generatedTenthPairProjection) := by
        rw [← LinearEquiv.mul_apply, ← map_mul, transport_product, map_mul,
          LinearEquiv.mul_apply]
      rw [pair_projection_transport, map_smul, hprojection,
        ← pair_projection_transport] at hc
      exact hc.symm
    have hnorm : leechIntegralAction g generatedTenthNormTwelveLine =
        generatedTenthNormTwelveLine ∨ leechIntegralAction g generatedTenthNormTwelveLine =
          -generatedTenthNormTwelveLine := by
      have hc : leechIntegralAction (generatedTenthE7TransportedSpatial g)
          generatedTenthE7NormTwelveLine =
          leechIntegralAction generatedTenthE7Isometry
            (leechIntegralAction g generatedTenthNormTwelveLine) := by
        rw [← generatedTenth_e7_norm_twelve_transport, ← LinearEquiv.mul_apply,
          ← map_mul, transport_product, map_mul, LinearEquiv.mul_apply]
      rcases hline with h | h
      · left
        apply (leechIntegralAction generatedTenthE7Isometry).injective
        rw [← hc, h, generatedTenth_e7_norm_twelve_transport]
      · right
        apply (leechIntegralAction generatedTenthE7Isometry).injective
        rw [← hc, h, map_neg, generatedTenth_e7_norm_twelve_transport]
    apply (generatedTenth_matrix_fix_flag_iff g).mpr
    refine ⟨hpair, ?_⟩
    rw [generatedTenth_norm_twelve_projection_line]
    exact (generatedIntegralLineMatrix_smul_fix_iff g _ original_line_ne_zero _
      (by norm_num)).mpr hnorm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
