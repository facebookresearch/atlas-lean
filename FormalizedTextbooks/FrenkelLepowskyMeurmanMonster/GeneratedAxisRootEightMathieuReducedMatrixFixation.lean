/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrixStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTransport

/-! The complete canonical matrix is fixed by the genuine reduced Mathieu compact lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The entire actual original root-eight matrix under the positive canonical spatial transport. -/
def generatedRootEightMathieuCanonicalMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  conwayMatrixAction generatedFifthRootEightCanonicalTransport
    (griessConwayEncode generatedFifthRootEightAxis).1

/-- Both reduced original permutations fix the complete actual canonical lattice flag. -/
theorem generatedRootEight_mathieu_reduced_flag (j : Fin 2) :
    leechIntegralAction (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j))
        leechNormSixHS100Root = leechNormSixHS100Root ∧
    leechIntegralAction (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j))
        leechNormSixHS100Companion = leechNormSixHS100Companion := by
  have hg : golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j) ∈
      Subgroup.closure (Set.range fun k =>
        golayPermutationIsometry (generatedRootEightMathieuReducedGenerator k)) :=
    Subgroup.subset_closure ⟨j, rfl⟩
  rw [generatedRootEight_mathieu_reduced_in_conway] at hg
  obtain ⟨g, _, he⟩ := Subgroup.mem_map.mp hg
  rw [← he]
  exact (leechNormSixActualPairStabilizer_mem _ _ _).mp g.property

/-- The complete canonical matrix is fixed, with every physical coordinate included. -/
theorem generatedRootEight_mathieu_reduced_canonical_matrix (j : Fin 2) :
    conwayMatrixAction (golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j))
      generatedRootEightMathieuCanonicalMatrix = generatedRootEightMathieuCanonicalMatrix := by
  let c := generatedFifthRootEightCanonicalTransport
  let g := golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j)
  let M := (griessConwayEncode generatedFifthRootEightAxis).1
  obtain ⟨hx, hy⟩ := generatedRootEight_mathieu_reduced_flag j
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
  have hg : c⁻¹ * g * c ∈ leechNormSixActualPairStabilizer
      generatedFifthRootEightNormFour generatedFifthRootEightNormSix := by
    apply (leechNormSixActualPairStabilizer_mem _ _ _).mpr
    constructor
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        generatedFifthRootEight_canonical_root, hx, hxi]
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        generatedFifthRootEight_canonical_companion, hy, hyi]
  have hm : conwayMatrixAction (c⁻¹ * g * c) M = M :=
    generatedFifthRootEight_point_stabilizer_le hg
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hm
  have hi : conwayMatrixAction c⁻¹ (conwayMatrixAction c M) = M := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact (conwayMatrixAction c⁻¹).injective (hm.trans hi.symm)

/-- Every genuine Q correction of the reduced compact lift fixes the whole actual canonical matrix. -/
theorem generatedRootEight_mathieu_reduced_corrected_matrix
    (h0 : generatedRootEightCompactSourceCondition 0)
    (h1 : generatedRootEightCompactSourceCondition 1)
    (h4 : generatedRootEightCompactSourceCondition 4)
    (h8 : generatedRootEightCompactSourceCondition 8) (q : Q) (j : Fin 2) :
    localMatrixRepresentation (generatedRootEightMathieuReducedCorrectedFiber h0 h1 h4 h8 q j)
      generatedRootEightMathieuCanonicalMatrix = generatedRootEightMathieuCanonicalMatrix := by
  change conwayMatrixAction
    (generatedRootEightMathieuReducedCorrectedFiber h0 h1 h4 h8 q j).val.2 _ = _
  rw [generatedRootEight_mathieu_reduced_corrected_spatial]
  exact generatedRootEight_mathieu_reduced_canonical_matrix j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
