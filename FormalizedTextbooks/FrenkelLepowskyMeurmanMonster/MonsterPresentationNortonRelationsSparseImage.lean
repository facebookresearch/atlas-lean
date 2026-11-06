/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Positive definiteness verifies entire actual images from finite sparse coordinate tests. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsDyadicPairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Correct norm and maximal pairing determine the entire actual generated-group image. -/
theorem monsterNortonGenerated_image_of_pairing (g : G) (x y : GriessSpace)
    (hp : griessForm (g.val x) y = griessForm x x)
    (hn : griessForm y y = griessForm x x) : g.val x = y := by
  have hg := generated_group_preserves_griessForm g x x
  have hs := form_symm y (g.val x)
  have hz : griessForm (g.val x - y) (g.val x - y) = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hg, hp, hs, hp, hn]
    ring
  exact sub_eq_zero.mp ((griessForm_self_eq_zero_iff _).mp hz)

private theorem form_sum_right {ι : Type*} [Fintype ι]
    (x : GriessSpace) (c : ι → ℝ) (v : ι → GriessSpace) :
    griessForm x (∑ i, c i • v i) = ∑ i, c i * griessForm x (v i) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

private theorem form_sum_left {ι : Type*} [Fintype ι]
    (x : GriessSpace) (c : ι → ℝ) (v : ι → GriessSpace) :
    griessForm (∑ i, c i • v i) x = ∑ i, c i * griessForm (v i) x := by
  rw [form_symm, form_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_symm]

/-- A sparse physical packet's norm is exactly its finite Gram-matrix quadratic expression. -/
theorem monsterNortonForm_sparse_packet {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → GriessSpace) :
    griessForm (∑ i, c i • v i) (∑ i, c i • v i) =
      ∑ i, ∑ j, c i * c j * griessForm (v i) (v j) := by
  rw [form_sum_left]
  simp_rw [form_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Only pairings on the packet support are required to certify the complete actual image. -/
theorem monsterNortonGenerated_image_of_sparse_pairings {ι : Type*} [Fintype ι]
    (g : G) (x : GriessSpace) (c : ι → ℝ) (v : ι → GriessSpace)
    (hp : (∑ i, c i * griessForm (g.val x) (v i)) = griessForm x x)
    (hn : (∑ i, ∑ j, c i * c j * griessForm (v i) (v j)) = griessForm x x) :
    g.val x = ∑ i, c i • v i := by
  apply monsterNortonGenerated_image_of_pairing
  · rw [form_sum_right]
    exact hp
  · rw [monsterNortonForm_sparse_packet]
    exact hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
