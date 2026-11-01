/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton U of order thirteen reduces line-pair powers to six seed distances. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineShift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal actual Norton line word at a natural exponent. -/
noncomputable def monsterNortonLineNatural (n : ℕ) : G :=
  y555NortonV * ((y555NortonActualU ^ n)⁻¹ *
    (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ n)⁻¹

/-- Every natural line exponent is its actual label modulo thirteen. -/
theorem monsterNortonLineNatural_mod (n : ℕ) :
    monsterNortonLineNatural n =
      y555NortonLine monsterSourceTriality ⟨n % 13, Nat.mod_lt _ (by decide)⟩ := by
  have h : y555NortonActualU ^ (n % 13) = y555NortonActualU ^ n := by
    simpa only [y555NortonActualU_orderOf] using pow_mod_orderOf y555NortonActualU n
  unfold monsterNortonLineNatural y555NortonLine y555NortonConjugate
  change y555NortonV * ((y555NortonActualU ^ n)⁻¹ *
    (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ n)⁻¹ =
      y555NortonV * ((y555NortonActualU ^ (n % 13))⁻¹ *
        (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (n % 13))⁻¹
  rw [h]

/-- Shifting both natural exponents is an exact conjugation of actual line ratios. -/
theorem monsterNortonLineNatural_shift (i j : ℕ) :
    monsterNortonLineNatural i * (monsterNortonLineNatural (i + j))⁻¹ =
      (y555NortonV * (y555NortonActualU ^ i)⁻¹ * y555NortonV⁻¹) *
        (monsterNortonLineNatural 0 * (monsterNortonLineNatural j)⁻¹) *
          (y555NortonV * (y555NortonActualU ^ i)⁻¹ * y555NortonV⁻¹)⁻¹ := by
  unfold monsterNortonLineNatural
  rw [Nat.add_comm i j, pow_add]
  simp only [pow_zero, inv_one, one_mul, mul_one]
  group

/-- Every periodic line-ratio power is equivalent to its first-line seed power. -/
theorem monsterNortonLineNatural_shift_pow_iff (i j k : ℕ) :
    (monsterNortonLineNatural i * (monsterNortonLineNatural (i + j))⁻¹) ^ k = 1 ↔
      (monsterNortonLineNatural 0 * (monsterNortonLineNatural j)⁻¹) ^ k = 1 := by
  rw [monsterNortonLineNatural_shift, conj_pow]
  constructor
  · intro h
    have h' := congrArg (fun x : G =>
      (y555NortonV * (y555NortonActualU ^ i)⁻¹ * y555NortonV⁻¹)⁻¹ * x *
        (y555NortonV * (y555NortonActualU ^ i)⁻¹ * y555NortonV⁻¹)) h
    convert h' using 1 <;> group
  · intro h
    rw [h, mul_one, mul_inv_cancel]

/-- Inverse distances have equivalent actual first-line power relations. -/
theorem monsterNortonLine_distance_complement (d : Fin 13) (hd : d ≠ 0) (k : ℕ) :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality d)⁻¹) ^ k = 1 ↔
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality ⟨13 - d.val, by
        have h : d.val ≠ 0 := fun h => hd (Fin.ext h)
        omega⟩)⁻¹) ^ k = 1 := by
  have hd0 : 0 < d.val := by
    have h : d.val ≠ 0 := fun h => hd (Fin.ext h)
    omega
  have hs := monsterNortonLineNatural_shift_pow_iff d.val (13 - d.val) k
  have hadd : d.val + (13 - d.val) = 13 := by omega
  rw [hadd, monsterNortonLineNatural_mod, monsterNortonLineNatural_mod,
    monsterNortonLineNatural_mod, monsterNortonLineNatural_mod] at hs
  simp only [Nat.mod_self, Nat.zero_mod, Nat.mod_eq_of_lt d.isLt,
    Nat.mod_eq_of_lt (show 13 - d.val < 13 by omega)] at hs
  have hinv : (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality d)⁻¹) ^ k = 1 ↔
      (y555NortonLine monsterSourceTriality d *
        (y555NortonLine monsterSourceTriality 0)⁻¹) ^ k = 1 := by
    have he : (y555NortonLine monsterSourceTriality 0 *
        (y555NortonLine monsterSourceTriality d)⁻¹)⁻¹ =
        y555NortonLine monsterSourceTriality d *
          (y555NortonLine monsterSourceTriality 0)⁻¹ := by group
    rw [← he, inv_pow, inv_eq_one]
  exact hinv.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
