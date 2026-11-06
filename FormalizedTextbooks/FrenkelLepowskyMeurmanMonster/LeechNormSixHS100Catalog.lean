/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100PairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100OctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100OddCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Transport

/-! A bijection onto every actual norm-four point of the genuine canonical flag, and its exact count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The original distinguished odd positions outside the two physical root coordinates. -/
abbrev LeechNormSixHS100OddPositions := {j : Fin 24 // j ≠ 0 ∧ j ≠ 1}

/-- One actual pair, all original octads containing the root pair, and all outside odd positions. -/
abbrev LeechNormSixHS100Labels :=
  Unit ⊕ (generatedFeasibleOctadContainingLabels ⊕ LeechNormSixHS100OddPositions)

/-- Every label retains its entire original genuine physical lattice vector and both flag pairings. -/
def leechNormSixHS100LabelPoint : LeechNormSixHS100Labels →
    LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion
  | Sum.inl _ => ⟨leechNormSixHS100Pair, leechNormSixHS100Pair_point⟩
  | Sum.inr (Sum.inl o) => ⟨leechNormSixHS100Octad o.val,
      leechNormSixHS100Octad_point o.val o.property⟩
  | Sum.inr (Sum.inr j) => ⟨leechNormSixHS100Odd j.val,
      leechNormSixHS100Odd_point j.val j.property.1 j.property.2⟩

private theorem pair_zero (u : Unit) :
    (leechNormSixHS100LabelPoint (Sum.inl u)).val.val 0 = 4 := by
  norm_num [leechNormSixHS100LabelPoint, leechNormSixHS100Pair, leechNormSixHS100PairIntegral]

private theorem octad_zero (o : generatedFeasibleOctadContainingLabels) :
    (leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o))).val.val 0 = 2 := by
  change (leechNormSixHS100Octad o.val).val 0 = 2
  rw [leechNormSixHS100Octad_coordinate]
  have h0 := (Finset.mem_filter.mp o.property).2.1
  simp only [Fin.val_zero, h0, ↓reduceIte]

private theorem odd_zero (j : LeechNormSixHS100OddPositions) :
    (leechNormSixHS100LabelPoint (Sum.inr (Sum.inr j))).val.val 0 = 1 := by
  change (leechNormSixHS100Odd j.val).val 0 = 1
  rw [leechNormSixHS100Odd_coordinate]
  simp [Ne.symm j.property.1]

/-- Exact physical coordinates distinguish the three families and every original label within them. -/
theorem leechNormSixHS100LabelPoint_injective : Function.Injective leechNormSixHS100LabelPoint := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · rw [Subsingleton.elim a b]
  · have he := congrArg (fun z => z.val.val 0) h
    rw [pair_zero, octad_zero] at he
    norm_num at he
  · have he := congrArg (fun z => z.val.val 0) h
    rw [pair_zero, odd_zero] at he
    norm_num at he
  · have he := congrArg (fun z => z.val.val 0) h
    rw [octad_zero, pair_zero] at he
    norm_num at he
  · have he := congrArg Subtype.val h
    change leechNormSixHS100Octad a.val = leechNormSixHS100Octad b.val at he
    have hab : a = b := Subtype.ext (leechNormSixHS100Octad_injective he)
    rw [hab]
  · have he := congrArg (fun z => z.val.val 0) h
    rw [octad_zero, odd_zero] at he
    norm_num at he
  · have he := congrArg (fun z => z.val.val 0) h
    rw [odd_zero, pair_zero] at he
    norm_num at he
  · have he := congrArg (fun z => z.val.val 0) h
    rw [odd_zero, octad_zero] at he
    norm_num at he
  · have he := congrArg Subtype.val h
    change leechNormSixHS100Odd a.val = leechNormSixHS100Odd b.val at he
    have hab : a = b := Subtype.ext (leechNormSixHS100Odd_injective he)
    rw [hab]

/-- The complete original shortest-vector catalogue covers every actual physical flag point. -/
theorem leechNormSixHS100LabelPoint_surjective : Function.Surjective leechNormSixHS100LabelPoint := by
  intro z
  obtain ⟨r, hr⟩ := leechShort_catalog z.val z.property.1
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · have he := leechNormSixHS100Pair_catalog z.val s p hr z.property
    exact ⟨Sum.inl (), Subtype.ext he.symm⟩
  · obtain ⟨ho, he⟩ := leechNormSixHS100Octad_catalog z.val o e hr z.property
    exact ⟨Sum.inr (Sum.inl ⟨o, ho⟩), Subtype.ext he.symm⟩
  · obtain ⟨h0, h1, he⟩ := leechNormSixHS100Odd_catalog z.val d j hr z.property
    exact ⟨Sum.inr (Sum.inr ⟨j, h0, h1⟩), Subtype.ext he.symm⟩

/-- The labels are a bijection onto the complete actual physical point set, without an orbit assumption. -/
def leechNormSixHS100CatalogEquiv : LeechNormSixHS100Labels ≃
    LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion :=
  Equiv.ofBijective leechNormSixHS100LabelPoint
    ⟨leechNormSixHS100LabelPoint_injective, leechNormSixHS100LabelPoint_surjective⟩

/-- The original outside distinguished positions have exactly twenty-two elements. -/
theorem leechNormSixHS100OddPositions_card : Nat.card LeechNormSixHS100OddPositions = 22 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The complete actual catalogue has one pair, seventy-seven octads, and twenty-two odd points. -/
theorem leechNormSixHS100Labels_card : Nat.card LeechNormSixHS100Labels = 100 := by
  rw [Nat.card_sum, Nat.card_sum, leechNormSixHS100OddPositions_card]
  have ho : Nat.card generatedFeasibleOctadContainingLabels = 77 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, generatedFeasibleOctadContainingLabels_card]
  rw [ho]
  norm_num

/-- The complete original norm-four point set of the canonical genuine flag has exactly one hundred vectors. -/
theorem leechNormSixHS100CanonicalPoints_card :
    Nat.card (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) = 100 :=
  (Nat.card_congr leechNormSixHS100CatalogEquiv.symm).trans leechNormSixHS100Labels_card

/-- Every actual norm-four/norm-six flag of pairing sixteen has exactly one hundred original physical points. -/
theorem leechNormSixHS100Points_card (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16) :
    Nat.card (LeechNormSixHS100Points x y) = 100 := by
  rw [leechNormSixHS100Points_card_transport x y hx hy hxy,
    leechNormSixHS100CanonicalPoints_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
