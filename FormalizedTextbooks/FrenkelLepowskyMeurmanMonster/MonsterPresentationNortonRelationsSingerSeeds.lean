/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine Singer conjugation propagates the first line square to distances three and four. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerV
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Square
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineSeeds

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine source Singer conjugation multiplies every actual natural line label by three. -/
theorem monsterNortonSinger_LineNatural (n : ℕ) :
    monsterNortonSingerGenerated⁻¹ * monsterNortonLineNatural n * monsterNortonSingerGenerated =
      monsterNortonLineNatural (3 * n) := by
  let φ : MulAut G := MulAut.conj monsterNortonSingerGenerated⁻¹
  have hu : φ y555NortonActualU = y555NortonActualU ^ 3 := by
    exact monsterNortonSinger_U_generated_conjugation
  have hv : φ y555NortonV = y555NortonV := by
    change monsterNortonSingerGenerated⁻¹ * y555NortonV * monsterNortonSingerGenerated = _
    rw [monsterNortonSingerGenerated_commute_V.inv_left.eq]
    group
  have ht : φ monsterSourceTriality = monsterSourceTriality := by
    change monsterNortonSingerGenerated⁻¹ * monsterSourceTriality *
      monsterNortonSingerGenerated = _
    rw [monsterNortonSingerGenerated_commute_sourceTriality.inv_left.eq]
    group
  change φ (monsterNortonLineNatural n) = _
  simp only [monsterNortonLineNatural, map_mul, map_inv, map_pow, hu, hv, ht, ← pow_mul]

/-- Every actual first-line seed power propagates to its triple distance. -/
theorem monsterNortonSinger_LineNatural_seed (n k : ℕ)
    (h : (monsterNortonLineNatural 0 * (monsterNortonLineNatural n)⁻¹) ^ k = 1) :
    (monsterNortonLineNatural 0 * (monsterNortonLineNatural (3 * n))⁻¹) ^ k = 1 := by
  have he : monsterNortonSingerGenerated⁻¹ *
      (monsterNortonLineNatural 0 * (monsterNortonLineNatural n)⁻¹) *
        monsterNortonSingerGenerated =
      monsterNortonLineNatural 0 * (monsterNortonLineNatural (3 * n))⁻¹ := by
    calc
      _ = (monsterNortonSingerGenerated⁻¹ * monsterNortonLineNatural 0 *
          monsterNortonSingerGenerated) *
          (monsterNortonSingerGenerated⁻¹ * monsterNortonLineNatural n *
            monsterNortonSingerGenerated)⁻¹ := by group
      _ = _ := by rw [monsterNortonSinger_LineNatural, monsterNortonSinger_LineNatural]
  have hp := conj_pow (i := k) (a := monsterNortonSingerGenerated⁻¹)
    (b := monsterNortonLineNatural 0 * (monsterNortonLineNatural n)⁻¹)
  simp only [inv_inv] at hp
  rw [← he, hp, h]
  group

private theorem natural_literal (n : ℕ) (d : Fin 13) (h : n % 13 = d.val) :
    monsterNortonLineNatural n = y555NortonLine monsterSourceTriality d := by
  rw [monsterNortonLineNatural_mod]
  congr 1
  exact Fin.ext h

private theorem first_natural_square :
    (monsterNortonLineNatural 0 * (monsterNortonLineNatural 1)⁻¹) ^ 2 = 1 := by
  rw [natural_literal 0 0 (by decide), natural_literal 1 1 (by decide)]
  exact monsterNortonLineZeroOne_square

/-- The actual first-line distance-three square follows by genuine Singer conjugation. -/
theorem monsterNortonLineZeroThree_square :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 3)⁻¹) ^ 2 = 1 := by
  have h := monsterNortonSinger_LineNatural_seed 1 2 first_natural_square
  simpa only [natural_literal 0 0 (by decide),
    natural_literal (3 * 1) 3 (by decide)] using h

/-- The actual first-line distance-nine square follows by a second genuine Singer conjugation. -/
theorem monsterNortonLineZeroNine_square :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 9)⁻¹) ^ 2 = 1 := by
  have h3 := monsterNortonSinger_LineNatural_seed 1 2 first_natural_square
  have h9 := monsterNortonSinger_LineNatural_seed 3 2 h3
  simpa only [natural_literal 0 0 (by decide),
    natural_literal (3 * 3) 9 (by decide)] using h9

/-- Complementing the actual distance-nine square proves the distance-four seed. -/
theorem monsterNortonLineZeroFour_square :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 4)⁻¹) ^ 2 = 1 := by
  exact (monsterNortonLine_distance_complement 9 (by decide) 2).mp
    monsterNortonLineZeroNine_square

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
