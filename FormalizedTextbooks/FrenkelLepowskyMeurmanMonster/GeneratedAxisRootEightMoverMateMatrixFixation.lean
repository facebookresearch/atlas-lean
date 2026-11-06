/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMatePositiveFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveMatrixBinding

/-! Both genuine positive flag moves fix the whole actual canonical matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- Preserving the original root and either complete companion orientation fixes the actual matrix. -/
theorem generatedRootEight_canonical_matrix_of_flag_or_mate (g : leechIsomSubgroup)
    (hx : leechIntegralAction g leechNormSixHS100Root = leechNormSixHS100Root)
    (hy : leechIntegralAction g leechNormSixHS100Companion = leechNormSixHS100Companion ∨
      leechIntegralAction g leechNormSixHS100Companion =
        leechNormSixHS100Root - leechNormSixHS100Companion) :
    conwayMatrixAction g generatedRootEightMathieuCanonicalMatrix =
      generatedRootEightMathieuCanonicalMatrix := by
  let c := generatedFifthRootEightCanonicalTransport
  let M := (griessConwayEncode generatedFifthRootEightAxis).1
  have hxi : leechIntegralAction c⁻¹ leechNormSixHS100Root = generatedFifthRootEightNormFour := by
    rw [← generatedFifthRootEight_canonical_root]
    change leechIntegralAction c⁻¹ (leechIntegralAction c generatedFifthRootEightNormFour) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hyi : leechIntegralAction c⁻¹ leechNormSixHS100Companion = generatedFifthRootEightNormSix := by
    rw [← generatedFifthRootEight_canonical_companion]
    change leechIntegralAction c⁻¹ (leechIntegralAction c generatedFifthRootEightNormSix) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hgr : leechIntegralAction (c⁻¹ * g * c) generatedFifthRootEightNormFour =
      generatedFifthRootEightNormFour := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFifthRootEight_canonical_root, hx, hxi]
  have hgy : leechIntegralAction (c⁻¹ * g * c) generatedFifthRootEightNormSix =
      generatedFifthRootEightNormSix ∨
      leechIntegralAction (c⁻¹ * g * c) generatedFifthRootEightNormSix =
        generatedFifthRootEightNormFour - generatedFifthRootEightNormSix := by
    rcases hy with hy | hy
    · left
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        generatedFifthRootEight_canonical_companion, hy, hyi]
    · right
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        generatedFifthRootEight_canonical_companion, hy, map_sub, hxi, hyi]
  have hgw : leechIntegralAction (c⁻¹ * g * c) generatedFifthRootEightNormTwenty =
      generatedFifthRootEightNormTwenty ∨
      leechIntegralAction (c⁻¹ * g * c) generatedFifthRootEightNormTwenty =
        -generatedFifthRootEightNormTwenty := by
    rcases hgy with hy | hy
    · left
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul, hgr, hy]
    · right
      rw [generatedFifthRootEightNormTwenty, map_sub, map_nsmul, hgr, hy]
      abel
  have hg : c⁻¹ * g * c ∈ generatedFifthRootEightMatrixStabilizer :=
    (generatedFifthRootEightMatrixStabilizer_mem _).mpr ⟨hgw, Or.inl hgr⟩
  have hm : conwayMatrixAction (c⁻¹ * g * c) M = M := hg
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hm
  have hi : conwayMatrixAction c⁻¹ (conwayMatrixAction c M) = M := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact (conwayMatrixAction c⁻¹).injective (hm.trans hi.symm)

/-- The complete genuine point mover fixes every actual canonical matrix coordinate. -/
theorem generatedRootEight_mover_canonical_matrix :
    conwayMatrixAction leechNormSixHS100PointMover generatedRootEightMathieuCanonicalMatrix =
      generatedRootEightMathieuCanonicalMatrix :=
  generatedRootEight_canonical_matrix_of_flag_or_mate _
    leechNormSixHS100PointMover_root_fixed (Or.inl leechNormSixHS100PointMover_companion_fixed)

/-- The complete genuine mate word fixes every actual canonical matrix coordinate. -/
theorem generatedRootEight_mate_canonical_matrix :
    conwayMatrixAction leechNormSixHS100MateOrientation generatedRootEightMathieuCanonicalMatrix =
      generatedRootEightMathieuCanonicalMatrix :=
  generatedRootEight_canonical_matrix_of_flag_or_mate _
    leechNormSixHS100MateOrientation_root
    (Or.inr leechNormSixHS100MateOrientation_companion)

/-- Every actual Q correction of the positive mover preserves the complete actual canonical matrix. -/
theorem generatedRootEight_mover_corrected_matrix (q : Q) :
    localMatrixRepresentation (localFiberIncl q * generatedRootEightMoverPositiveFiber)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 := by
  rw [generatedRootEight_canonical_positive_matrix_actual]
  change conwayMatrixAction (1 * generatedRootEightMoverPositiveFiber.val.2) _ = _
  rw [one_mul, generatedRootEight_mover_positive_spatial]
  exact generatedRootEight_mover_canonical_matrix

/-- Every actual Q correction of the positive mate preserves the complete actual canonical matrix. -/
theorem generatedRootEight_mate_corrected_matrix (q : Q) :
    localMatrixRepresentation (localFiberIncl q * generatedRootEightMatePositiveFiber)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 := by
  rw [generatedRootEight_canonical_positive_matrix_actual]
  change conwayMatrixAction (1 * generatedRootEightMatePositiveFiber.val.2) _ = _
  rw [one_mul, generatedRootEight_mate_positive_spatial]
  exact generatedRootEight_mate_canonical_matrix

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
