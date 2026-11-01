/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPairPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The actual triality conjugate of a zero-pair-phase permutation has unsigned matrix action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine pair coefficient is relabeled without phase by the specified local lift. -/
theorem generatedSeventh_permutation_pair_coordinate (p : golayAutomorphismSubgroup)
    (f : localFiberSubgroup) (hf : f.val.2 = golayPermutationIsometry p)
    (hphase : ∀ s : Fin 2, ∀ k : Fin 276, localShortPhase f (Sum.inl (s, k)) = 0)
    (X : GriessShortIndex → ℝ) (s : Fin 2) (i j : Fin 24) (hij : i ≠ j) :
    localShortOperator f X (Sum.inl (s, griessPairIndex i j hij)) =
      X (Sum.inl (s, griessPairIndex (p.val.symm i) (p.val.symm j)
        (p.val.symm.injective.ne hij))) := by
  have h := localShortOperator_image f X (Sum.inl (s,
    griessPairIndex (p.val.symm i) (p.val.symm j) (p.val.symm.injective.ne hij)))
  rw [hf, generatedSeventh_unsigned_pair_permutation, hphase, qSign_zero, one_mul] at h
  simpa only [Equiv.apply_symm_apply] using h

/-- Conjugating the actual lift by triality gives the original unsigned permutation matrix action.
The assertion concerns the whole genuine matrix block, not only a representative. -/
theorem generatedSeventh_permutation_conjugate_matrix (p : golayAutomorphismSubgroup)
    (f : localFiberSubgroup) (hf : f.val.2 = golayPermutationIsometry p)
    (hphase : ∀ s : Fin 2, ∀ k : Fin 276, localShortPhase f (Sum.inl (s, k)) = 0)
    (x : GriessSpace) :
    (griessConwayEncode
      (sExtra (rhoLocal (localFiberIntoH f) (sExtra⁻¹ x)))).1 =
      conwayMatrixAction (golayPermutationIsometry p) (griessConwayEncode x).1 := by
  ext i j
  rw [generatedSeventh_permutation_matrix]
  by_cases hij : i = j
  · subst j
    rw [generatedFourth_triality_matrix_diagonal, generatedFourth_local_matrix, hf,
      generatedSeventh_permutation_matrix]
    have h := generatedFourth_triality_matrix_diagonal (sExtra⁻¹ x) (p.val.symm i)
    simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h.symm
  · rw [generatedFourth_triality_matrix_off_diagonal _ i j hij,
      generatedFourth_local_short,
      generatedSeventh_permutation_pair_coordinate p f hf hphase,
      generatedSeventh_permutation_pair_coordinate p f hf hphase]
    have h := generatedFourth_triality_matrix_off_diagonal (sExtra⁻¹ x)
      (p.val.symm i) (p.val.symm j) (p.val.symm.injective.ne hij)
    simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
