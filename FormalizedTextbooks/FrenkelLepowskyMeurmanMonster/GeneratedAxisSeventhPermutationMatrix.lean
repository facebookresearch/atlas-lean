/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMonomialSigns

/-! Genuine permutation action on the original seventh triangle projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Pulling a coordinate functional through the actual permutation relabels its basis vector. -/
theorem generatedSeventh_permutation_inverse_single (p : golayAutomorphismSubgroup)
    (i : Fin 24) :
    (golayPermutationIsometry p).val.symm (Pi.single i 1) = Pi.single (p.val.symm i) (1 : ℝ) := by
  ext j
  change (Pi.single i (1 : ℝ) : Fin 24 → ℝ) (p.val j) =
    (Pi.single (p.val.symm i) (1 : ℝ) : Fin 24 → ℝ) j
  have he : p.val j = i ↔ j = p.val.symm i := p.val.eq_symm_apply.symm
  simp only [Pi.single_apply, he]

/-- Every matrix coefficient has its genuine inverse-permutation coordinate address. -/
theorem generatedSeventh_permutation_matrix (p : golayAutomorphismSubgroup)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (i j : Fin 24) :
    conwayMatrixAction (golayPermutationIsometry p) M i j = M (p.val.symm i) (p.val.symm j) := by
  calc
    _ = Matrix.toBilin' (conwayMatrixAction (golayPermutationIsometry p) M)
        (Pi.single i 1) (Pi.single j 1) := (Matrix.toBilin'_single _ i j).symm
    _ = Matrix.toBilin' M ((golayPermutationIsometry p).val.symm (Pi.single i 1))
        ((golayPermutationIsometry p).val.symm (Pi.single j 1)) :=
      conwayMatrixAction_pairing _ _ _ _
    _ = Matrix.toBilin' M (Pi.single (p.val.symm i) 1) (Pi.single (p.val.symm j) 1) := by
      rw [generatedSeventh_permutation_inverse_single, generatedSeventh_permutation_inverse_single]
    _ = _ := Matrix.toBilin'_single _ _ _

/-- The original physical triangle as a three-coordinate finite set. -/
def generatedSeventhTriangleCoordinates : Finset (Fin 24) := {16, 17, 19}

/-- Preserving the actual triangle set preserves every coefficient of its spatial projection. -/
theorem generatedSeventh_permutation_plane_fixed (p : golayAutomorphismSubgroup)
    (hp : p • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates) :
    conwayMatrixAction (golayPermutationIsometry p) generatedSeventhPlaneSupport =
      generatedSeventhPlaneSupport := by
  have ht (i : Fin 24) : generatedSeventhTriangle (p.val.symm i) ↔
      generatedSeventhTriangle i := by
    have hmem : p • (p.val.symm i) ∈ p • generatedSeventhTriangleCoordinates ↔
        p.val.symm i ∈ generatedSeventhTriangleCoordinates :=
      Finset.smul_mem_smul_finset_iff p
    rw [hp] at hmem
    have hpi : p • (p.val.symm i) = i := p.val.apply_symm_apply i
    rw [hpi] at hmem
    simpa only [generatedSeventhTriangleCoordinates, Finset.mem_insert,
      Finset.mem_singleton, generatedSeventhTriangle] using hmem.symm
  ext i j
  rw [generatedSeventh_permutation_matrix]
  change (generatedSeventhPlaneNumerator (p.val.symm i) (p.val.symm j) : ℝ) =
    (generatedSeventhPlaneNumerator i j : ℝ)
  simp only [generatedSeventhPlaneNumerator, ht, p.val.symm.injective.eq_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
