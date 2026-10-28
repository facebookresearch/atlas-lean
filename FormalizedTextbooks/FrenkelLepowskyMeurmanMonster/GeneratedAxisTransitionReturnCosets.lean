/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyTransition

/-! The genuine first-to-first transition cosets in the actual local group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Source transition inputs are left Ω cosets in the actual local group. -/
abbrev generatedAxisTransitionCosetSpace := Quotient (QuotientGroup.rightRel localOmegaStabilizer)

/-- The actual transition domain consists of 16,584,750 genuine cosets. -/
theorem generatedAxisTransitionCosetSpace_card :
    Nat.card generatedAxisTransitionCosetSpace = 16584750 := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    localOmegaStabilizer), ← Subgroup.index_eq_card]
  exact localOmegaStabilizer_index

/-- Inclusion of the first-axis stabilizer induces the actual transition coset map. -/
noncomputable def generatedAxisReturnCosetMap (p : Fin 276) :
    Quotient (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p)) →
      generatedAxisTransitionCosetSpace :=
  Quotient.map' Subtype.val (by
    intro a b hab
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    exact hab)

/-- The map loses no feasible transition cosets. -/
theorem generatedAxisReturnCosetMap_injective (p : Fin 276) :
    Function.Injective (generatedAxisReturnCosetMap p) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro hab
      apply Quotient.sound'
      have he := Quotient.exact' hab
      rw [QuotientGroup.rightRel_apply] at he ⊢
      exact he

/-- Exactly 93,150 genuine transition cosets come from the first-axis stabilizer. -/
theorem generatedAxisReturnCosetMap_range_card (p : Fin 276) :
    Nat.card (Set.range (generatedAxisReturnCosetMap p)) = 93150 := by
  rw [← Nat.card_congr (Equiv.ofInjective _ (generatedAxisReturnCosetMap_injective p)),
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (localFeasibleTransitionSubgroup p)), ← Subgroup.index_eq_card]
  exact localFeasibleTransitionSubgroup_index p

/-- The genuine transition cosets whose actual triality images return to the first local orbit. -/
noncomputable def generatedAxisFirstReturnCosets (p : Fin 276) :
    Set generatedAxisTransitionCosetSpace :=
  {c | ∃ h : H, Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h = c ∧
    sExtra (rhoLocal h (conwayAxis p)) ∈ generatedSignedShortAxes}

/-- A local element returns to the first orbit precisely when its image lies in the
actual signed-pair orbit of the genuine Ω centralizer. -/
theorem generatedAxis_triality_local_first_return_iff (p : Fin 276) (h : H) :
    sExtra (rhoLocal h (conwayAxis p)) ∈ generatedSignedShortAxes ↔
      rhoLocal h (conwayAxis p) ∈ generatedSignedPairAxes := by
  have hx : rhoLocal h (conwayAxis p) ∈ generatedSignedShortAxes := by
    rw [← generatedAxisLocalOrbit_eq_signed (Sum.inl (0, p)) 0]
    exact ⟨h, by rw [conwayShortAxis_pair_zero]⟩
  obtain ⟨⟨s, c⟩, he⟩ := hx
  rw [← he, generatedAxis_triality_first_return_iff]
  constructor
  · rintro ⟨t, r, hr⟩
    refine ⟨((t, r), c), ?_⟩
    change conwayShortAxis (Sum.inl (t, r)) c = conwayShortAxis s c
    change s = Sum.inl (t, r) at hr
    rw [hr]
  · rintro ⟨⟨⟨t, r⟩, d⟩, hv⟩
    have hi := @generatedAxis_signed_injective (Sum.inl (t, r), d) (s, c) hv
    exact ⟨t, r, (congrArg Prod.fst hi).symm⟩

/-- The actual returning transition cosets are exactly the image of the first-axis stabilizer. -/
theorem generatedAxisFirstReturnCosets_eq_range (p : Fin 276) :
    generatedAxisFirstReturnCosets p = Set.range (generatedAxisReturnCosetMap p) := by
  ext c
  constructor
  · rintro ⟨h, rfl, hh⟩
    have hx := (generatedAxis_triality_local_first_return_iff p h).mp hh
    rw [← generatedAxis_localOmega_pair_orbit_eq p] at hx
    obtain ⟨n, hn⟩ := hx
    let a : H := n.val⁻¹ * h
    have ha : a ∈ localAxisStabilizer p := by
      change rhoLocal (n.val⁻¹ * h) (conwayAxis p) = conwayAxis p
      rw [rhoLocal.map_mul]
      change rhoLocal n.val⁻¹ (rhoLocal h (conwayAxis p)) = conwayAxis p
      rw [← hn, rhoLocal.map_inv]
      exact (rhoLocal n.val).symm_apply_apply _
    refine ⟨Quotient.mk (QuotientGroup.rightRel (localFeasibleTransitionSubgroup p))
      (⟨a, ha⟩ : localAxisStabilizer p), ?_⟩
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    change h * a⁻¹ ∈ localOmegaStabilizer
    have he : h * a⁻¹ = n.val := by dsimp [a]; group
    rw [he]
    exact n.property
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with
    | h a =>
      refine ⟨a.val, rfl, ?_⟩
      rw [a.property, conwayAxis_triality, ← conwayShortAxis_pair_zero p]
      exact ⟨(Sum.inl (0, p), 0), rfl⟩

/-- The actual first-to-first transition coefficient is 93,150, without an assumed table entry. -/
theorem generatedAxisFirstReturnCosets_card (p : Fin 276) :
    Nat.card (generatedAxisFirstReturnCosets p) = 93150 := by
  rw [generatedAxisFirstReturnCosets_eq_range]
  exact generatedAxisReturnCosetMap_range_card p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
