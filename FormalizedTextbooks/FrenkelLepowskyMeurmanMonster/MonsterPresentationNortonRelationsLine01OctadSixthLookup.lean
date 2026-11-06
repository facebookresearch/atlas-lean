/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact extraction of each actual sixth octad coefficient from its unique source summand. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadCatalogueData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem source_match_iff (a : Fin 64) (k j : Fin 16) (e : Fin 64) :
    (monsterNortonLine01ShortInverseIsOctad a = true ∧
      monsterNortonLine01ShortInverseOctadId a k = j ∧
      monsterNortonLine01ShortInverseOctadSigns a k = e) ↔
    (monsterNortonLine01OctadSignSupport e ∧
      a = monsterNortonLine01OctadSourceA j (monsterNortonLine01OctadSignLookup e) ∧
      k = monsterNortonLine01OctadSourceK j (monsterNortonLine01OctadSignLookup e)) := by
  constructor
  · rintro ⟨ha, hj, he⟩
    have h := monsterNortonLine01OctadSource_left a k ha
    rw [hj, he] at h
    exact ⟨h.1, h.2.1.symm, h.2.2.symm⟩
  · rintro ⟨hs, rfl, rfl⟩
    have h := monsterNortonLine01OctadSource_right j (monsterNortonLine01OctadSignLookup e)
    exact ⟨h.1, h.2.1, h.2.2.trans hs⟩

private theorem double_sum_single {α β E : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid E] (f : α → β → E)
    (A : α) (K : β) :
    (∑ a : α, ∑ k : β, if a = A ∧ k = K then f a k else 0) = f A K := by
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const_zero]

/-- The single original source coefficient occupying an actual reached octad coordinate. -/
def monsterNortonLine01OctadSixthSourceLookup (j : Fin 16) (e : Fin 64) : ℤ :=
  if monsterNortonLine01OctadSignSupport e then
    monsterNortonLine01ShortSixthSourceCoefficient
      (monsterNortonLine01OctadSourceA j (monsterNortonLine01OctadSignLookup e))
      (monsterNortonLine01OctadSourceK j (monsterNortonLine01OctadSignLookup e)) else 0

/-- The full actual finite octad sum is exactly its unique supported source lookup. -/
theorem monsterNortonLine01OctadSixthSourceLookup_actual (j : Fin 16) (e : Fin 64) :
    monsterNortonLine01OctadSixthNumerator j e =
      monsterNortonLine01OctadSixthSourceLookup j e := by
  unfold monsterNortonLine01OctadSixthNumerator monsterNortonLine01OctadSixthSourceLookup
  simp_rw [source_match_iff]
  by_cases h : monsterNortonLine01OctadSignSupport e
  · simp only [h, true_and, ite_true]
    exact double_sum_single _ _ _
  · simp only [h, false_and, ite_false, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
