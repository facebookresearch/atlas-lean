/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact unique-source lookup for every reached sixth odd-short coordinate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OddCatalogueData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem slot_cast (i : Fin 24) (hi : i.val < 16) :
    (⟨(monsterNortonLine01OddPhysicalSlot i).val, by omega⟩ : Fin 24) = i := by
  apply Fin.ext
  simp only [monsterNortonLine01OddPhysicalSlot, Nat.mod_eq_of_lt hi]

private theorem source_match_iff (a : Fin 64) (k : Fin 16) (d : Fin 2048) (i : Fin 24) :
    (monsterNortonLine01ShortInverseIsOctad a = false ∧
      monsterNortonLine01ShortInverseOddCode a k = d ∧
      monsterNortonLine01ShortInverseOddCoordinate a k = i) ↔
    (monsterNortonLine01OddCodeSupport d ∧ i.val < 16 ∧
      a = monsterNortonLine01OddSourceA (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i) ∧
      k = monsterNortonLine01OddSourceK (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i)) := by
  constructor
  · rintro ⟨ha, hd, hi⟩
    have h := monsterNortonLine01OddSource_left a k ha
    have hp := monsterNortonLine01OddOutput_physical a k ha
    rw [hd, hi] at h
    rw [hi] at hp
    exact ⟨h.1, hp, h.2.1.symm, h.2.2.symm⟩
  · rintro ⟨hs, hi, rfl, rfl⟩
    have h := monsterNortonLine01OddSource_right (monsterNortonLine01OddCodeLookup d)
      (monsterNortonLine01OddPhysicalSlot i)
    exact ⟨h.1, h.2.1.trans hs, h.2.2.trans (slot_cast i hi)⟩

private theorem double_sum_single {α β E : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid E] (f : α → β → E)
    (A : α) (K : β) :
    (∑ a : α, ∑ k : β, if a = A ∧ k = K then f a k else 0) = f A K := by
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const_zero]

/-- The unique original source coefficient occupying a reached sixth odd-short coordinate. -/
def monsterNortonLine01OddSixthSourceLookup (d : Fin 2048) (i : Fin 24) : ℤ :=
  if monsterNortonLine01OddCodeSupport d ∧ i.val < 16 then
    monsterNortonLine01ShortSixthSourceCoefficient
      (monsterNortonLine01OddSourceA (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i))
      (monsterNortonLine01OddSourceK (monsterNortonLine01OddCodeLookup d)
        (monsterNortonLine01OddPhysicalSlot i)) else 0

/-- The entire actual odd-short sum reduces to its unique supported source coefficient. -/
theorem monsterNortonLine01OddSixthSourceLookup_actual (d : Fin 2048) (i : Fin 24) :
    monsterNortonLine01OddSixthNumerator d i = monsterNortonLine01OddSixthSourceLookup d i := by
  unfold monsterNortonLine01OddSixthNumerator monsterNortonLine01OddSixthSourceLookup
  simp_rw [source_match_iff]
  by_cases hd : monsterNortonLine01OddCodeSupport d
  · by_cases hi : i.val < 16
    · simp only [hd, hi, true_and, ite_true]
      exact double_sum_single _ _ _
    · simp only [hd, hi, true_and, false_and, ite_false, Finset.sum_const_zero]
  · simp only [hd, false_and, ite_false, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
