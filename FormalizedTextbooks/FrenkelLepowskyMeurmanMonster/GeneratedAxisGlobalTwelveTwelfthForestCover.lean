/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestShard15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! The complete checked Twelfth binary singular forest and the resulting actual coverage.

The sixteen shards check the descent obligations of all `2 ^ 24` coordinate masks. Since every
parent operator is the actual inverse action of a whole-axis fixer of `generatedTwelfthAxis`,
strictly decreasing proposed ranks give coverage of the genuine binary Ω orbit by the stabilizer
orbits of the thirty-eight Ω roots; the short-class and zero roots are excluded by norms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 4096 blocks of the forest evaluate to `true`. -/
theorem generatedAxisGlobalTwelveTwelfthForest_block (k g t : Fin 16) :
    generatedAxisGlobalTwelveTwelfthLoopB
      (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
        (16 * (16 * k.val + g.val) + t.val)) (4096 * (16 * (16 * k.val + g.val) + t.val)) 12 0 =
      true := by
  fin_cases k
  · exact generatedAxisGlobalTwelveTwelfthForestShard00 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard01 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard02 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard03 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard04 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard05 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard06 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard07 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard08 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard09 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard10 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard11 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard12 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard13 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard14 g t
  · exact generatedAxisGlobalTwelveTwelfthForestShard15 g t

/-- The descent obligation holds at every bounded coordinate mask. -/
theorem generatedAxisGlobalTwelveTwelfthForest_complete (b : ℕ) (hb : b < 2 ^ 24) :
    generatedAxisGlobalTwelveTwelfthForestStep b := by
  have hj : b / 4096 < 4096 := by omega
  have hk : b / 4096 / 256 < 16 := by omega
  have hblk := generatedAxisGlobalTwelveTwelfthForest_block ⟨b / 4096 / 256, hk⟩
    ⟨b / 4096 / 16 % 16, Nat.mod_lt _ (by decide)⟩ ⟨b / 4096 % 16, Nat.mod_lt _ (by decide)⟩
  have he : 16 * (16 * (b / 4096 / 256) + b / 4096 / 16 % 16) + b / 4096 % 16 = b / 4096 := by
    omega
  change generatedAxisGlobalTwelveTwelfthLoopB
    (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
      (16 * (16 * (b / 4096 / 256) + b / 4096 / 16 % 16) + b / 4096 % 16))
    (4096 * (16 * (16 * (b / 4096 / 256) + b / 4096 / 16 % 16) + b / 4096 % 16)) 12 0 =
      true at hblk
  rw [he] at hblk
  have h := generatedAxisGlobalTwelveTwelfthBlock_sound (b / 4096) hj hblk (b % 4096)
    (Nat.mod_lt _ (by decide))
  rwa [show 4096 * (b / 4096) + b % 4096 = b by omega] at h

set_option maxHeartbeats 4000000 in
-- Check the 144 parent column masks against the coordinate bound.
/-- Every parent column mask has only the twenty-four genuine coordinate bits. -/
theorem generatedAxisGlobalTwelveTwelfthParentColumns_lt : ∀ e : Fin 6, ∀ j : Fin 24,
    generatedAxisGlobalTwelveTwelfthParentColumns e j < 2 ^ 24 := by
  decide +kernel

/-- Every parent of a bounded mask stays in the bounded mask domain. -/
theorem generatedAxisGlobalTwelveTwelfthParent_lt (e : Fin 6) (b : ℕ) :
    generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthParentColumns e) b <
      2 ^ 24 := by
  rw [← generatedAxisGlobalMaskRowsAction_ofFn]
  apply generatedAxisGlobalMaskRowsAction_lt
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact generatedAxisGlobalTwelveTwelfthParentColumns_lt e j

/-- The actual binary Ω orbit is covered by the Twelfth stabilizer orbits of the Ω roots. -/
theorem generatedAxisGlobalTwelveTwelfthBinary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ k : Fin 38, ∃ c : H,
      c ∈ generatedTwelfthLocalAxisStabilizer ∧
        co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode
          (generatedAxisGlobalTwelveTwelfthOmegaRootMask k)) = x.val := by
  let encode := (generatedAxisGlobalMaskFiniteEquiv 24).symm
  let rank : generatedAxisGlobalBinaryOrbit → ℕ :=
    fun x => generatedAxisGlobalTwelveTwelfthRank (encode x.val).val
  have hmain : ∀ n x, rank x = n → ∃ k : Fin 38, ∃ c : H,
      c ∈ generatedTwelfthLocalAxisStabilizer ∧
        co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode
          (generatedAxisGlobalTwelveTwelfthOmegaRootMask k)) = x.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      let b := encode x.val
      have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
        (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
      have hs : generatedAxisGlobalMaskSingular b.val = true := by
        rw [generatedAxisGlobalMaskSingular_iff, hb]
        exact generatedAxisGlobalBinary_squareQuad x
      rcases generatedAxisGlobalTwelveTwelfthForest_complete b.val b.isLt hs with hr | ⟨e, hlt⟩
      · obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveTwelfthForestRoot_omega b.val hr (by
          rw [hb]
          exact x.property)
        refine ⟨k, 1, Subgroup.one_mem _, ?_⟩
        rw [map_one, map_one, hk, hb]
        rfl
      · let g : H := (generatedAxisGlobalTwelveTwelfthGenerator e).val
        let y := generatedAxisGlobalBinaryAct g⁻¹ x
        let p := generatedAxisGlobalMaskColumnAction
          (generatedAxisGlobalTwelveTwelfthParentColumns e) b.val
        have hp : p < 2 ^ 24 := generatedAxisGlobalTwelveTwelfthParent_lt e b.val
        have hy : y.val = monsterCo1GeometryBinaryMaskDecode p := by
          change co1BinaryAction (projH g⁻¹) x.val = _
          rw [generatedAxisGlobalTwelveTwelfthGenerator_parent, ← hb,
            generatedAxisGlobalMaskColumnAction_decode]
        have hyb : encode y.val = (⟨p, hp⟩ : Fin (2 ^ 24)) := by
          apply (generatedAxisGlobalMaskFiniteEquiv 24).injective
          rw [Equiv.apply_symm_apply]
          exact hy
        have hyr : rank y < rank x := by
          change generatedAxisGlobalTwelveTwelfthRank (encode y.val).val <
            generatedAxisGlobalTwelveTwelfthRank b.val
          rw [hyb]
          exact hlt
        obtain ⟨k, c, hc, hk⟩ := ih (rank y) (hx ▸ hyr) y rfl
        refine ⟨k, g * c,
          Subgroup.mul_mem _ (generatedAxisGlobalTwelveTwelfthGenerator e).property hc, ?_⟩
        rw [map_mul, map_mul, LinearEquiv.mul_apply, hk]
        change co1BinaryAction (projH g) (co1BinaryAction (projH g⁻¹) x.val) = x.val
        rw [map_inv, map_inv]
        exact LinearEquiv.apply_symm_apply _ _
  intro x
  exact hmain (rank x) x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
