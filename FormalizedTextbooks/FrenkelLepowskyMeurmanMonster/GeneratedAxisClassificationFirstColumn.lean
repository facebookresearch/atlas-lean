/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFiberCounts

/-! Exact counting of the three actual destinations in the first transition
column. Source: Höhn–Seysen, arXiv:2508.01037, Table 2, first column. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An injectively labelled genuine short family enumerates its actual
triality destination fiber, when the family criterion has been proved. -/
theorem generatedAxis_short_family_fiber_card {ι : Type*}
    (f : ι → GriessShortIndex) (hf : Function.Injective f)
    (c : generatedAxisLocalOrbitSpace)
    (hclass : ∀ r δ, Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (conwayShortAxis r δ)) = c ↔ r ∈ Set.range f) :
    Nat.card (generatedAxisTransitionAxisFiber c) = Nat.card ι * 2 := by
  let g : ι × ZMod 2 → generatedAxisTransitionAxisFiber c := fun a =>
    ⟨⟨conwayShortAxis (f a.1) a.2, ⟨(f a.1, a.2), rfl⟩⟩,
      (hclass (f a.1) a.2).mpr ⟨a.1, rfl⟩⟩
  have hi : Function.Injective g := by
    intro a b h
    have hv : conwayShortAxis (f a.1) a.2 = conwayShortAxis (f b.1) b.2 :=
      congrArg (fun y : generatedAxisTransitionAxisFiber c => y.val.val) h
    have hp := @generatedAxis_signed_injective (f a.1, a.2) (f b.1, b.2) hv
    have hfst : f a.1 = f b.1 := congrArg (fun p : GriessShortIndex × ZMod 2 => p.1) hp
    have hsnd : a.2 = b.2 := congrArg (fun p : GriessShortIndex × ZMod 2 => p.2) hp
    exact Prod.ext (hf hfst) hsnd
  have hu : Function.Surjective g := by
    rintro ⟨⟨x, ⟨⟨r, δ⟩, hx⟩⟩, hc⟩
    change conwayShortAxis r δ = x at hx
    change Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra x) = c at hc
    rw [← hx] at hc
    obtain ⟨i, hi⟩ := (hclass r δ).mp hc
    refine ⟨(i, δ), Subtype.ext (Subtype.ext ?_)⟩
    change conwayShortAxis (f i) δ = x
    rw [hi, hx]
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hi, hu⟩), Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

/-- Exactly 97,152 actual signed-short axes have the octad destination. -/
theorem generatedAxis_octad_axis_fiber_card :
    Nat.card (generatedAxisTransitionAxisFiber generatedAxisOctadDestination) = 97152 := by
  have h := generatedAxis_short_family_fiber_card
    (fun a : Fin 759 × Fin 64 => Sum.inr (Sum.inl a))
    (Sum.inr_injective.comp Sum.inl_injective) generatedAxisOctadDestination (by
      intro r δ
      apply (generatedAxis_triality_octad_class_iff r δ).trans
      constructor
      · rintro ⟨o, e, he⟩; exact ⟨(o, e), he.symm⟩
      · rintro ⟨⟨o, e⟩, he⟩; exact ⟨o, e, he.symm⟩)
  rw [h]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

/-- Exactly 98,304 actual signed-short axes have the odd destination. -/
theorem generatedAxis_odd_axis_fiber_card :
    Nat.card (generatedAxisTransitionAxisFiber generatedAxisOddDestination) = 98304 := by
  have h := generatedAxis_short_family_fiber_card
    (fun a : Fin 2048 × Fin 24 => Sum.inr (Sum.inr a))
    (Sum.inr_injective.comp Sum.inr_injective) generatedAxisOddDestination (by
      intro r δ
      apply (generatedAxis_triality_odd_class_iff r δ).trans
      constructor
      · rintro ⟨d, i, he⟩; exact ⟨(d, i), he.symm⟩
      · rintro ⟨⟨d, i⟩, he⟩; exact ⟨d, i, he.symm⟩)
  rw [h]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

/-- The actual octad destination contains 8,197,200 genuine transition cosets. -/
theorem generatedAxis_octad_transition_fiber_card (p : Fin 276) :
    Nat.card (generatedAxisTransitionDestination p ⁻¹' {generatedAxisOctadDestination}) =
      8197200 := by
  have h := generatedAxisTransition_fiber_balance_normalized p generatedAxisOctadDestination
  rw [generatedAxis_octad_axis_fiber_card] at h
  omega

/-- The actual odd destination contains 8,294,400 genuine transition cosets. -/
theorem generatedAxis_odd_transition_fiber_card (p : Fin 276) :
    Nat.card (generatedAxisTransitionDestination p ⁻¹' {generatedAxisOddDestination}) =
      8294400 := by
  have h := generatedAxisTransition_fiber_balance_normalized p generatedAxisOddDestination
  rw [generatedAxis_odd_axis_fiber_card] at h
  omega

/-- Every genuine transition coset from the first local axis orbit has one
of these three actual local destinations. This is exhaustive for this column. -/
theorem generatedAxis_first_column_destinations (p : Fin 276)
    (t : generatedAxisTransitionCosetSpace) :
    generatedAxisTransitionDestination p t =
        Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p) ∨
      generatedAxisTransitionDestination p t = generatedAxisOctadDestination ∨
        generatedAxisTransitionDestination p t = generatedAxisOddDestination := by
  induction t using Quotient.inductionOn with
  | h h =>
    have hx : rhoLocal h (conwayAxis p) ∈ generatedSignedShortAxes := by
      rw [← generatedAxisLocalActual_orbit_eq_signed p]
      exact ⟨h, rfl⟩
    obtain ⟨⟨r, δ⟩, hr⟩ := hx
    change conwayShortAxis r δ = rhoLocal h (conwayAxis p) at hr
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra (rhoLocal h (conwayAxis p))) =
          Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p) ∨
      Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra (rhoLocal h (conwayAxis p))) = generatedAxisOctadDestination ∨
      Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra (rhoLocal h (conwayAxis p))) = generatedAxisOddDestination
    rw [← hr]
    rcases r with ⟨s, q⟩ | (⟨o, e⟩ | ⟨d, i⟩)
    · apply Or.inl
      apply Quotient.sound'
      rw [MulAction.orbitRel_apply, generatedAxisLocalActual_orbit_eq_signed p]
      exact generatedAxis_triality_pair_mem_signed q s δ
    · exact Or.inr (Or.inl ((generatedAxis_triality_octad_class_iff _ δ).mpr ⟨o, e, rfl⟩))
    · exact Or.inr (Or.inr ((generatedAxis_triality_odd_class_iff _ δ).mpr ⟨d, i, rfl⟩))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
