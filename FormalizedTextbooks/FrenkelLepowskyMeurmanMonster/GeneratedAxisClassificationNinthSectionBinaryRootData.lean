/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction

/-! Connected original root pairings control signs in the actual binary section kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An earlier nonorthogonal root for each noninitial original E8 basis root. -/
def generatedNinthSectionRootParent : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 1, 6]

/-- The actual physical real embedding of the original lattice root basis. -/
def generatedNinthSectionRealRoot (j : Fin 8) : Fin 24 → ℝ :=
  leechCoordinateEmbedding (generatedFifthFrameRoot j).val

/-- The root-pair tree is acyclic in the original eight-basis ordering. -/
theorem generatedNinth_section_root_parent_lt : ∀ j : Fin 8, j ≠ 0 →
    (generatedNinthSectionRootParent j).val < j.val := by
  decide +kernel

/-- Every noninitial root has a nonzero actual integral pairing with its stated parent. -/
theorem generatedNinth_section_root_integer_pair_ne_zero : ∀ j : Fin 8, j ≠ 0 →
    (∑ i : Fin 24,
      generatedFifthFrameInsert
        (generatedOctadIntegerRootMatrix.col (generatedNinthSectionRootParent j)) i *
      generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j) i : ℤ) ≠ 0 := by
  decide +kernel

private theorem cross_pairing (u v : Fin 24 → ℤ) :
    stdPairingFun (leechCoordinateEmbedding u) (leechCoordinateEmbedding v) =
      (∑ i : Fin 24, u i * v i : ℤ) / (8 : ℝ) := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := by
    simpa only [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  simp only [stdPairingFun, leechCoordinateEmbedding, Int.cast_sum, Int.cast_mul,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change ((u i : ℝ) / Real.sqrt 8) * ((v i : ℝ) / Real.sqrt 8) =
    (u i : ℝ) * (v i : ℝ) / 8
  rw [div_mul_div_comm, hs]

/-- Every noninitial physical root has a nonzero actual real pairing with its parent. -/
theorem generatedNinth_section_root_pair_ne_zero (j : Fin 8) (hj : j ≠ 0) :
    generatedNinthSectionRealRoot (generatedNinthSectionRootParent j) ⬝ᵥ
      generatedNinthSectionRealRoot j ≠ 0 := by
  change stdPairingFun _ _ ≠ 0
  rw [generatedNinthSectionRealRoot, generatedNinthSectionRealRoot,
    generatedFifthFrameRoot_physical, generatedFifthFrameRoot_physical, cross_pairing]
  apply div_ne_zero _ (by norm_num)
  exact_mod_cast generatedNinth_section_root_integer_pair_ne_zero j hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
