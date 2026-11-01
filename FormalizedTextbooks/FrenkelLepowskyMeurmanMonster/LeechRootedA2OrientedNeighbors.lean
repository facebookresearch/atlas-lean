/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadCoordinates

/-! The actual lattice vectors on the positive side of the standard root pairing. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine lattice neighbors of 4(e0+e1), with the positive pairing orientation. -/
abbrev leechRootedA2OrientedNeighbor :=
  {v : leechIntegral // leechSquareSum v.val = 32 ∧ v.val 0 + v.val 1 = 4}

/-- Choose the unique original short-vector sign with positive root pairing. -/
noncomputable def leechRootedA2Orient (r : leechRootedA2NeighborAddress) :
    leechRootedA2OrientedNeighbor :=
  if h : griessShortIntegral r.val 0 + griessShortIntegral r.val 1 = 4 then
    ⟨⟨griessShortIntegral r.val, griessShortIntegral_mem r.val⟩,
      griessShortIntegral_squareSum r.val, h⟩
  else
    ⟨⟨-griessShortIntegral r.val, leechIntegral.neg_mem (griessShortIntegral_mem r.val)⟩,
      by rw [leechSquareSum_neg, griessShortIntegral_squareSum], by
        have hn := r.property.resolve_left h
        change -griessShortIntegral r.val 0 + -griessShortIntegral r.val 1 = 4
        omega⟩

/-- Distinct genuine catalogue addresses cannot orient to the same lattice vector. -/
theorem leechRootedA2Orient_injective : Function.Injective leechRootedA2Orient := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun v : leechRootedA2OrientedNeighbor => v.val.val) h
  unfold leechRootedA2Orient at he
  split_ifs at he with ha hb hb
  · exact griessShort_label_unique a.val b.val (Or.inl he)
  · exact griessShort_label_unique a.val b.val (Or.inr he)
  · exact griessShort_label_unique a.val b.val (Or.inr (neg_eq_iff_eq_neg.mp he))
  · exact griessShort_label_unique a.val b.val (Or.inl (neg_injective he))

/-- Every genuine norm-four lattice neighbor comes from its actual catalogue address. -/
theorem leechRootedA2Orient_surjective : Function.Surjective leechRootedA2Orient := by
  intro v
  obtain ⟨r, hr | hr⟩ := leechShort_catalog v.val v.property.1
  · have h : griessShortIntegral r 0 + griessShortIntegral r 1 = 4 := by
      rw [← hr]
      exact v.property.2
    refine ⟨⟨r, Or.inl h⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [leechRootedA2Orient, h, dite_true]
    exact hr.symm
  · have h : griessShortIntegral r 0 + griessShortIntegral r 1 = -4 := by
      have hv := v.property.2
      rw [hr] at hv
      change -griessShortIntegral r 0 + -griessShortIntegral r 1 = 4 at hv
      omega
    have hn : griessShortIntegral r 0 + griessShortIntegral r 1 ≠ 4 := by omega
    refine ⟨⟨r, Or.inr h⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [leechRootedA2Orient, hn, dite_false]
    exact hr.symm

/-- The catalogue and actual oriented lattice neighbors are faithfully equivalent. -/
noncomputable def leechRootedA2OrientedNeighborEquiv :
    leechRootedA2NeighborAddress ≃ leechRootedA2OrientedNeighbor :=
  Equiv.ofBijective leechRootedA2Orient
    ⟨leechRootedA2Orient_injective, leechRootedA2Orient_surjective⟩

/-- Finiteness comes from the actual finite short-vector catalogue. -/
noncomputable instance : Fintype leechRootedA2OrientedNeighbor :=
  Fintype.ofEquiv leechRootedA2NeighborAddress leechRootedA2OrientedNeighborEquiv

/-- There are exactly4600 actual lattice vectors with the positive root pairing. -/
theorem leechRootedA2OrientedNeighbor_card :
    Fintype.card leechRootedA2OrientedNeighbor = 4600 := by
  rw [← Fintype.card_congr leechRootedA2OrientedNeighborEquiv,
    leechRootedA2NeighborAddress_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
