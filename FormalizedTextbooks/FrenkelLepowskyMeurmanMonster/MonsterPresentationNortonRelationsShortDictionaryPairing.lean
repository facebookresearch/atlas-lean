/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite code and coordinate tests for the actual preferred-short Gram matrix. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual preferred-short Gram matrix is the ordinary unit matrix. -/
theorem monsterNortonPureShort_form (r s : GriessShortIndex) :
    griessForm (monsterNortonPureShort r) (monsterNortonPureShort s) =
      if r = s then 1 else 0 := by
  rw [monsterNortonForm_pureShort_right, monsterNortonPureShort,
    monsterNortonShortProjection_short]
  by_cases h : r = s
  · subst s
    simp only [Pi.single_eq_same, ite_true]
  · simp only [Pi.single_eq_of_ne (Ne.symm h), ite_eq_right h]

/-- Comparing two genuine octad indices requires only their source Golay codes. -/
theorem monsterNortonOctadIndex_eq_iff (a b : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (hb : golayMaskWeight (golayEncodedMask b.val) = 8) :
    monsterNortonOctadIndex a ha = monsterNortonOctadIndex b hb ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg golayOctadLabel h
    simpa only [monsterNortonOctadIndex_label] using hc
  · intro h
    subst b
    rfl

/-- Ordered physical coordinates determine the actual pair index without enumeration. -/
theorem monsterNortonOrderedPairIndex_eq_iff (a b c d : Fin 24)
    (hab : a < b) (hcd : c < d) :
    griessPairIndex a b (ne_of_lt hab) = griessPairIndex c d (ne_of_lt hcd) ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    have hc := congrArg griessCoordinatePair h
    simpa only [griessPairIndex_coordinates, hab, hcd, ite_true, Prod.mk.injEq] using hc
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Actual octad-short pairings reduce to finite code and local sign-label equality. -/
theorem monsterNortonOctadShort_form (a b : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (hb : golayMaskWeight (golayEncodedMask b.val) = 8) (e f : Fin 64) :
    griessForm
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))))
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex b hb, f)))) =
        if a = b ∧ e = f then 1 else 0 := by
  rw [monsterNortonPureShort_form]
  simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
    monsterNortonOctadIndex_eq_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
