/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

/-! Every actual Mathieu flag permutation preserves the genuine sixth-axis spatial matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A physical coordinate permutation transports each original coordinate basis vector. -/
theorem leechRootedA2_permutation_single (p : Equiv.Perm (Fin 24)) (a : Fin 24) :
    golayRealPermute p (Pi.single a (1 : ℝ)) = Pi.single (p a) 1 := by
  ext i
  have h : p.symm i = a ↔ i = p a := p.symm_apply_eq
  simp only [golayRealPermute_apply, Pi.single_apply, h]

/-- The original physical matrix action relabels both indices by the inverse permutation. -/
theorem leechRootedA2_permutation_matrix (p : golayAutomorphismSubgroup)
    (a : Matrix (Fin 24) (Fin 24) ℝ) (i j : Fin 24) :
    conwayMatrixAction (golayPermutationIsometry p) a i j = a (p.val.symm i) (p.val.symm j) := by
  rw [← Matrix.toBilin'_single
    (conwayMatrixAction (golayPermutationIsometry p) a) i j, conwayMatrixAction_pairing]
  have hi : (golayPermutationIsometry p).val.symm (Pi.single i (1 : ℝ)) =
      Pi.single (p.val.symm i) 1 := leechRootedA2_permutation_single p.val.symm i
  have hj : (golayPermutationIsometry p).val.symm (Pi.single j (1 : ℝ)) =
      Pi.single (p.val.symm j) 1 := leechRootedA2_permutation_single p.val.symm j
  rw [hi, hj, Matrix.toBilin'_single]

/-- The sparse actual matrix has an unordered-pair expression independent of coordinate ordering. -/
theorem leechRootedA2Sixth_matrix_unordered (i j : Fin 24) :
    generatedSixthAxisMatrix i j =
      if i = j then
        if i = 19 then 33 / 32 else if i = 16 ∨ i = 17 then 17 / 32 else 9 / 32
      else if (i = 16 ∧ j = 17) ∨ (i = 17 ∧ j = 16) then 1 / 8
      else if ((i = 16 ∨ i = 17) ∧ j = 19) ∨
        (i = 19 ∧ (j = 16 ∨ j = 17)) then -3 / 8 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [generatedSixthAxisMatrix, generatedSixthMiddlePairValue]

/-- Every genuine unordered-root-pair permutation fixes the complete original spatial matrix. -/
theorem leechRootedA2Sixth_permutation_spatial (p : golayAutomorphismSubgroup)
    (hp : p ∈ leechRootedA2SixthPermutationFlag) :
    golayPermutationIsometry p ∈ generatedSixthSpatialStabilizer := by
  change conwayMatrixAction _ (griessConwayEncode generatedSixthAxis).1 = _
  rw [generatedSixth_axis_matrix]
  ext i j
  rw [leechRootedA2_permutation_matrix, leechRootedA2Sixth_matrix_unordered,
    leechRootedA2Sixth_matrix_unordered]
  have h19 : ∀ k, p.val.symm k = 19 ↔ k = 19 := by
    intro k
    rw [p.val.symm_apply_eq, hp.2]
  have hij : p.val.symm i = p.val.symm j ↔ i = j := p.val.symm.injective.eq_iff
  rcases hp.1 with hp | hp
  · have h16 : ∀ k, p.val.symm k = 16 ↔ k = 16 := by
      intro k
      rw [p.val.symm_apply_eq, hp.1]
    have h17 : ∀ k, p.val.symm k = 17 ↔ k = 17 := by
      intro k
      rw [p.val.symm_apply_eq, hp.2]
    simp only [hij, h16, h17, h19]
  · have h16 : ∀ k, p.val.symm k = 16 ↔ k = 17 := by
      intro k
      rw [p.val.symm_apply_eq, hp.1]
    have h17 : ∀ k, p.val.symm k = 17 ↔ k = 16 := by
      intro k
      rw [p.val.symm_apply_eq, hp.2]
    simp only [hij, h16, h17, h19]
    simp only [or_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
