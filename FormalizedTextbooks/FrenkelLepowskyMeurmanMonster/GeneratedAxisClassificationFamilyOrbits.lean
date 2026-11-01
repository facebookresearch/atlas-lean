/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationMonomialFamilies
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionDestinations

/-! The three actual local destinations of triality on the first axis orbit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equality in the actual local orbit space is genuine transport by H. -/
theorem generatedAxis_local_class_eq_iff (x y : GriessSpace) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) x =
      Quotient.mk (MulAction.orbitRel H GriessSpace) y ↔
        ∃ h : H, rhoLocal h x = y := by
  constructor
  · intro he
    have h := MulAction.orbitRel_apply.mp (Quotient.exact' he)
    exact MulAction.mem_orbit_symm.mp h
  · intro h
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_symm.mp h

/-- Every signed octad axis has zero tensor coordinate after triality. -/
theorem generatedAxis_triality_octad_family_tensor_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.2 = 0 := by
  funext t i
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, trialityCycle]

private theorem signed_preserved (h : H) (x : GriessSpace)
    (hx : x ∈ generatedSignedShortAxes) : rhoLocal h x ∈ generatedSignedShortAxes := by
  rw [← generatedAxisLocalOrbit_eq_signed (Sum.inl (0, 0)) 0] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨h * k, ?_⟩
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hk]

private theorem triality_monomial_class (r s : GriessShortIndex)
    (e : leechIsomSubgroup) (he : e ∈ golayMonomialSubgroup)
    (hlabel : griessShortPermutation e r = s) (c d : ZMod 2) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (conwayShortAxis r c)) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (conwayShortAxis s d)) := by
  obtain ⟨n, hn⟩ := generatedAxis_monomial_signed_localOmega r s e he hlabel c d
  obtain ⟨h, hh⟩ := localOmegaStabilizer_triality_orbit n (conwayShortAxis r c)
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  refine ⟨h, ?_⟩
  rw [hh, hn]

/-- The actual octad-family destination, with an original dictionary representative. -/
noncomputable def generatedAxisOctadDestination : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0))

/-- The actual odd-family destination, with an original dictionary representative. -/
noncomputable def generatedAxisOddDestination : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0))

/-- All and only octad-family signed axes have the actual octad destination. -/
theorem generatedAxis_triality_octad_class_iff (r : GriessShortIndex) (c : ZMod 2) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (conwayShortAxis r c)) =
      generatedAxisOctadDestination ↔
        ∃ o : Fin 759, ∃ e : Fin 64, r = Sum.inr (Sum.inl (o, e)) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · constructor
    · intro he
      obtain ⟨h, hh⟩ := (generatedAxis_local_class_eq_iff _ _).mp he
      have hs := signed_preserved h _ (generatedAxis_triality_pair_mem_signed p s c)
      rw [hh] at hs
      exact False.elim (generatedAxis_triality_octad_not_signed 0 0 hs)
    · rintro ⟨_, _, he⟩
      cases he
  · constructor
    · exact fun _ => ⟨o, e, rfl⟩
    · intro _
      obtain ⟨a, ha, hl⟩ := generatedAxis_octad_monomial_transitive o 0 e 0
      exact triality_monomial_class _ _ a ha hl c 0
  · constructor
    · intro he
      obtain ⟨h, hh⟩ := (generatedAxis_local_class_eq_iff _ _).mp he.symm
      have hz := generatedAxis_local_preserves_tensor_zero h _
        (generatedAxis_triality_octad_tensor_zero 0 0)
      rw [hh] at hz
      exact False.elim (generatedAxis_triality_odd_tensor_ne_zero d i c hz)
    · rintro ⟨_, _, he⟩
      cases he

/-- All and only odd-family signed axes have the actual odd destination. -/
theorem generatedAxis_triality_odd_class_iff (r : GriessShortIndex) (c : ZMod 2) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (conwayShortAxis r c)) =
      generatedAxisOddDestination ↔
        ∃ d : Fin 2048, ∃ i : Fin 24, r = Sum.inr (Sum.inr (d, i)) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · constructor
    · intro he
      obtain ⟨h, hh⟩ := (generatedAxis_local_class_eq_iff _ _).mp he
      have hs := signed_preserved h _ (generatedAxis_triality_pair_mem_signed p s c)
      rw [hh] at hs
      exact False.elim (generatedAxis_triality_odd_not_signed 0 0 0 hs)
    · rintro ⟨_, _, he⟩
      cases he
  · constructor
    · intro he
      obtain ⟨h, hh⟩ := (generatedAxis_local_class_eq_iff _ _).mp he
      have hz := generatedAxis_local_preserves_tensor_zero h _
        (generatedAxis_triality_octad_family_tensor_zero o e c)
      rw [hh] at hz
      exact False.elim (generatedAxis_triality_odd_tensor_ne_zero 0 0 0 hz)
    · rintro ⟨_, _, he⟩
      cases he
  · constructor
    · exact fun _ => ⟨d, i, rfl⟩
    · intro _
      obtain ⟨a, ha, hl⟩ := generatedAxis_odd_monomial_transitive d 0 i 0
      exact triality_monomial_class _ _ a ha hl c 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
