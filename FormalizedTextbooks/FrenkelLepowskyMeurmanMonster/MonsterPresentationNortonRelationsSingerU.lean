/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual source Singer permutation conjugates literal Norton U to its cube in G. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerUSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerUIsometry

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fiber_intertwines (e f : localFiberSubgroup) (n : ℕ)
    (hs : e.val.1 * f.val.1 = f.val.1 ^ n * e.val.1)
    (hl : e.val.2 * f.val.2 = f.val.2 ^ n * e.val.2) : e * f = f ^ n * e := by
  apply Subtype.ext
  apply Prod.ext
  · change e.val.1 * f.val.1 = f.val.1 ^ n * e.val.1
    exact hs
  · change e.val.2 * f.val.2 = f.val.2 ^ n * e.val.2
    exact hl

/-- Both exact fiber components give the actual Singer/U intertwining relation. -/
theorem monsterNortonSinger_U_fiber_intertwines :
    monsterNortonSingerFiber * monsterNortonUFiber =
      monsterNortonUFiber ^ 3 * monsterNortonSingerFiber :=
  fiber_intertwines _ _ _ monsterNortonSinger_U_spin_intertwines
    monsterNortonSinger_U_leech_intertwines

/-- The complete local source lift intertwines Norton U with its cube in G. -/
theorem monsterNortonSinger_U_generated_intertwines :
    localIntoGenerated monsterNortonSingerLocal * y555NortonActualU =
      y555NortonActualU ^ 3 * localIntoGenerated monsterNortonSingerLocal := by
  have h := congrArg (QuotientGroup.mk' localDiagonalSubgroup)
    monsterNortonSinger_U_fiber_intertwines
  rw [map_mul, map_mul, map_pow] at h
  have hg := congrArg localIntoGenerated h
  rw [map_mul, map_mul, map_pow] at hg
  change localIntoGenerated monsterNortonSingerLocal *
      localIntoGenerated monsterNortonULocal =
    (localIntoGenerated monsterNortonULocal) ^ 3 *
      localIntoGenerated monsterNortonSingerLocal at hg
  rw [monsterNortonULocal_generated] at hg
  exact hg

/-- The literal inverse-permutation convention gives the genuine Singer normalizer of U. -/
theorem monsterNortonSinger_U_generated_conjugation :
    monsterNortonSingerGenerated⁻¹ * y555NortonActualU * monsterNortonSingerGenerated =
      y555NortonActualU ^ 3 := by
  simp only [monsterNortonSingerGenerated, map_inv, inv_inv]
  rw [monsterNortonSinger_U_generated_intertwines]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
