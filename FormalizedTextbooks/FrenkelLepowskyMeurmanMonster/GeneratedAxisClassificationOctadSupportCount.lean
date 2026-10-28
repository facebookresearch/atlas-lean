/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupport
public import Mathlib.Data.Finset.Prod

/-! The actual octad transition has exactly 120 nonzero short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The unordered coordinate pairs within the eight-element octad support. -/
def generatedOctadOrderedPairs (o : Fin 759) : Finset (Fin 24 × Fin 24) :=
  let s := golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)
  (s ×ˢ s).filter (fun p => p.1 < p.2)

/-- The actual 276-pair catalogue restricts bijectively to these ordered pairs. -/
noncomputable def generatedOctadPairSupportEquiv (o : Fin 759) :
    {p : Fin 276 // generatedOctadPairSupport o p} ≃ generatedOctadOrderedPairs o where
  toFun p := ⟨griessCoordinatePair p.val, by
    have hp := (griessCoordinatePairEquiv p.val).property
    simp only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    change (griessCoordinatePair p.val).1 < (griessCoordinatePair p.val).2 at hp
    simpa only [generatedOctadOrderedPairs, Finset.mem_filter, Finset.mem_product,
      golayMaskSupport, Finset.mem_univ, true_and, generatedOctadPairSupport]
      using And.intro p.property hp⟩
  invFun p := by
    have hp : (golayEncodedMask (golayOctadLabel o).val).testBit p.val.1.val = true ∧
        (golayEncodedMask (golayOctadLabel o).val).testBit p.val.2.val = true ∧
        p.val.1 < p.val.2 := by
      simpa only [generatedOctadOrderedPairs, Finset.mem_filter, Finset.mem_product,
        golayMaskSupport, Finset.mem_univ, true_and, and_assoc] using p.property
    let v : griessCoordinatePairs := ⟨p.val, by
      simpa only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and]
        using hp.2.2⟩
    refine ⟨griessCoordinatePairEquiv.symm v, ?_⟩
    have hv : griessCoordinatePair (griessCoordinatePairEquiv.symm v) = p.val :=
      congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply v)
    simp only [generatedOctadPairSupport, hv]
    exact ⟨hp.1, hp.2.1⟩
  left_inv p := by
    apply Subtype.ext
    exact griessCoordinatePairEquiv.symm_apply_apply p.val
  right_inv p := by
    apply Subtype.ext
    dsimp only
    simp only [griessCoordinatePair, Equiv.apply_symm_apply]

/-- Exactly 28 coordinate pairs lie inside an actual octad. -/
theorem generatedOctad_pair_support_card (o : Fin 759) :
    Nat.card {p : Fin 276 // generatedOctadPairSupport o p} = 28 := by
  rw [Nat.card_congr (generatedOctadPairSupportEquiv o), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  change ((golayMaskSupport (golayEncodedMask (golayOctadLabel o).val) ×ˢ
    golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)).filter
      (fun p => p.1 < p.2)).card = 28
  rw [Finset.card_product_filter_lt, golayOctad_support_card]
  decide

/-- The supported short labels are two signs per pair and 64 octad signs. -/
noncomputable def generatedOctadShortSupportEquiv (o : Fin 759) :
    {r : GriessShortIndex // generatedOctadShortSupport o r} ≃
      (Fin 2 × {p : Fin 276 // generatedOctadPairSupport o p}) ⊕ Fin 64 where
  toFun r := match r with
    | ⟨Sum.inl (s, p), h⟩ => Sum.inl (s, ⟨p, h⟩)
    | ⟨Sum.inr (Sum.inl (_, e)), _⟩ => Sum.inr e
    | ⟨Sum.inr (Sum.inr _), h⟩ => False.elim h
  invFun
    | Sum.inl (s, p) => ⟨Sum.inl (s, p.val), p.property⟩
    | Sum.inr e => ⟨Sum.inr (Sum.inl (o, e)), rfl⟩
  left_inv r := by
    rcases r with ⟨(⟨s, p⟩ | (⟨p, e⟩ | ⟨d, i⟩)), h⟩
    · rfl
    · change p = o at h
      subst p
      rfl
    · exact False.elim h
  right_inv r := by rcases r with ⟨s, p⟩ | e <;> rfl

/-- Exactly 120 actual short labels occur in an octad transition. -/
theorem generatedOctad_short_support_card (o : Fin 759) :
    Nat.card {r : GriessShortIndex // generatedOctadShortSupport o r} = 120 := by
  rw [Nat.card_congr (generatedOctadShortSupportEquiv o), Nat.card_sum, Nat.card_prod,
    generatedOctad_pair_support_card]
  norm_num

/-- The actual nonzero-coordinate set, rather than a proposed abstract list,
has cardinality 120. -/
theorem generatedAxis_triality_octad_nonzero_short_card
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    Nat.card {r : GriessShortIndex //
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r ≠ 0}
      = 120 := by
  have he : {r : GriessShortIndex //
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r ≠ 0} ≃
      {r : GriessShortIndex // generatedOctadShortSupport o r} :=
    Equiv.subtypeEquivRight (fun r => generatedAxis_triality_octad_support_iff o e c r)
  rw [Nat.card_congr he, generatedOctad_short_support_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
