/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A finite orthonormal packet identifies a whole actual vector by supported reads and norm. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Norm and supported coefficients of an orthonormal packet determine the entire vector. -/
theorem monsterNortonOrthonormalPacket_identifies {I : Type*} [Fintype I] [DecidableEq I]
    (x : GriessSpace) (c : I → ℝ) (v : I → GriessSpace)
    (hv : ∀ i j, griessForm (v i) (v j) = if i = j then 1 else 0)
    (hc : ∀ i, griessForm x (v i) = c i)
    (hn : griessForm x x = ∑ i, c i ^ 2) : x = ∑ i, c i • v i := by
  let y := ∑ i, c i • v i
  have hyy : griessForm y y = ∑ i, c i ^ 2 := monsterNortonOrthonormalPacket_norm c v hv
  have hxy : griessForm x y = ∑ i, c i ^ 2 := by
    dsimp only [y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, hc, pow_two]
  have hyx : griessForm y x = ∑ i, c i ^ 2 := (form_symm y x).trans hxy
  have hz : griessForm (x - y) (x - y) = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hn, hxy, hyx, hyy]
    ring
  exact sub_eq_zero.mp ((griessForm_self_eq_zero_iff _).mp hz)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
