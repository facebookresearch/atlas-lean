/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal Norton word has order dividing thirteen on the actual Leech lattice. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem action_power (e : leechIsomSubgroup)
    (A : Matrix (Fin 24) (Fin 24) ℝ)
    (h : ∀ x : Fin 24 → ℝ, e.val x = A *ᵥ x) (n : ℕ) (x : Fin 24 → ℝ) :
    (e ^ n).val x = (A ^ n) *ᵥ x := by
  induction n generalizing x with
  | zero => simp
  | succ n hn =>
    change ((e ^ n) * e).val x = _
    change (e ^ n).val (e.val x) = _
    rw [hn, h, Matrix.mulVec_mulVec, ← pow_succ]

/-- The actual lattice component of the literal Norton word has thirteenth power one. -/
theorem monsterNortonUFiber_leech_thirteen : monsterNortonUFiber.val.2 ^ 13 = 1 := by
  have h : (monsterNortonUMatrixQ.map (Rat.castHom ℝ)) ^ 13 = 1 := by
    have h := congrArg (Rat.castHom ℝ).mapMatrix monsterNortonUMatrixQ_thirteen
    rw [map_pow, map_one] at h
    exact h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [action_power _ _ monsterNortonUFiber_leech_matrix, h, Matrix.one_mulVec]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
