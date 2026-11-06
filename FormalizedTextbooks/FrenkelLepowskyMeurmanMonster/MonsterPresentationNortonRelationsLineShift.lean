/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact conjugation normalization of actual Norton line-pair words. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPointLineAll
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Translating both line labels conjugates their actual parameter ratio. -/
theorem monsterNortonLinePair_shift_word (i j : Fin 13) (hij : i.val + j.val < 13) :
    y555NortonLine monsterSourceTriality i *
      (y555NortonLine monsterSourceTriality ⟨i.val + j.val, hij⟩)⁻¹ =
    (y555NortonV * (y555NortonActualU ^ i.val)⁻¹ * y555NortonV⁻¹) *
      (y555NortonLine monsterSourceTriality 0 *
        (y555NortonLine monsterSourceTriality j)⁻¹) *
      (y555NortonV * (y555NortonActualU ^ i.val)⁻¹ * y555NortonV⁻¹)⁻¹ := by
  unfold y555NortonLine y555NortonConjugate
  change y555NortonV *
      (((y555NortonActualU ^ i.val)⁻¹ * (y555NortonV * monsterSourceTriality) *
        y555NortonActualU ^ i.val)⁻¹) *
      (y555NortonV * (((y555NortonActualU ^ (i.val + j.val))⁻¹ *
        (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (i.val + j.val))⁻¹))⁻¹ = _
  rw [Nat.add_comm i.val j.val, pow_add]
  simp only [Fin.val_zero, pow_zero, inv_one, one_mul, mul_one]
  unfold y555NortonActualU
  group

/-- Any line-pair power relation is exactly the corresponding first-line difference relation. -/
theorem monsterNortonLinePair_shift_pow_iff (i j : Fin 13) (hij : i.val + j.val < 13)
    (k : ℕ) :
    (y555NortonLine monsterSourceTriality i *
      (y555NortonLine monsterSourceTriality ⟨i.val + j.val, hij⟩)⁻¹) ^ k = 1 ↔
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality j)⁻¹) ^ k = 1 := by
  rw [monsterNortonLinePair_shift_word, conj_pow]
  constructor
  · intro h
    have h' := congrArg
      (fun x => (y555NortonV * (y555NortonActualU ^ i.val)⁻¹ * y555NortonV⁻¹)⁻¹ * x *
        (y555NortonV * (y555NortonActualU ^ i.val)⁻¹ * y555NortonV⁻¹)) h
    convert h' using 1 <;> group
  · intro h
    rw [h, mul_one, mul_inv_cancel]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
