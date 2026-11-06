/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Verified A,B,C dictionary rows of the actual y82 spin/Leech pair. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Pairs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine lattice sign gives the physical A row of the candidate. -/
theorem monsterSourceY82_blocks_A (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.1 0 p =
      qSign (monsterY82PairCharacter p) * (trialityBlocksEquiv x).2.1 0 p := by
  have he := localGriessRepresentation_encode monsterSourceY82Fiber x
  have hm := congrArg (fun b : ConwayRawSpace => b.1) he
  change (griessConwayEncode (rhoLocal monsterSourceY82Local x)).1 =
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode 82))
      (griessConwayEncode x).1 at hm
  have hp := congrFun (congrFun hm (griessCoordinatePair p).1) (griessCoordinatePair p).2
  rw [sourceGeneratedSign_matrix_apply] at hp
  simpa only [griessConwayEncode, dite_false, griessCoordinatePair_ne,
    griessPairIndex_pair, monsterY82PairCharacter, monsterSourceY82Code] using hp

/-- The two actual short pair coordinates give the source B and C dictionary rows. -/
theorem monsterSourceY82_blocks_BC (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.1 1 p =
      (trialityBlocksEquiv x).2.1 1 p ∧
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.1 2 p =
      qSign (monsterY82PairCharacter p) * (trialityBlocksEquiv x).2.1 2 p := by
  have he := localGriessRepresentation_encode monsterSourceY82Fiber x
  have h0 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (0,p))) he
  have h1 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (1,p))) he
  change (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.1 (Sum.inl (0,p)) =
    localShortRepresentation monsterSourceY82Fiber (griessConwayEncode x).2.1
      (Sum.inl (0,p)) at h0
  change (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.1 (Sum.inl (1,p)) =
    localShortRepresentation monsterSourceY82Fiber (griessConwayEncode x).2.1
      (Sum.inl (1,p)) at h1
  change _ = localShortOperator monsterSourceY82Fiber (griessConwayEncode x).2.1
    (Sum.inl (0,p)) at h0
  change _ = localShortOperator monsterSourceY82Fiber (griessConwayEncode x).2.1
    (Sum.inl (1,p)) at h1
  rw [monsterSourceY82_pair_operator] at h0 h1
  have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  rcases hc (monsterY82PairCharacter p) with h | h
  · simp only [monsterY82PairColor, h, ite_true, qSign_zero, one_mul,
      griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1 ⊢
    constructor <;> linarith
  · simp only [monsterY82PairColor, h, show (1 : ZMod 2) ≠ 0 by decide,
      ite_false, Equiv.swap_apply_left, Equiv.swap_apply_right, qSign_one,
      griessConwayEncode, ite_true, ite_false] at h0 h1 ⊢
    constructor <;> linarith

/-- All candidate A,B,C rows match the literal source triality word. -/
theorem monsterSourceY82_blocks_ABC_match (x : GriessSpace) (a : Fin 3) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.1 a p =
      (trialityBlocksEquiv
        ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).2.1 a p := by
  rw [monsterSourceYWord_blocks_ABC]
  have hc : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide +kernel
  rcases hc a with rfl | rfl | rfl
  · simpa only [show (0 : Fin 3) ≠ 1 by decide, ite_false,
      monsterY82PairCharacter, monsterSourceY82Code] using
      monsterSourceY82_blocks_A x p
  · simpa only [ite_true, one_mul] using (monsterSourceY82_blocks_BC x p).1
  · simpa only [show (2 : Fin 3) ≠ 1 by decide, ite_false,
      monsterY82PairCharacter, monsterSourceY82Code] using
      (monsterSourceY82_blocks_BC x p).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
