/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits

/-! Triality destinations for arbitrary actual Griess vectors. The source
certificate in Höhn--Seysen §3.2 must check these destinations for every listed
local representative, rather than only for the first signed-short axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual local orbit classes of a triality image are constant on Ω cosets,
for every vector, including all later source representatives. -/
theorem generatedAxisGlobal_destination_congr (x : GriessSpace) (a b : H)
    (hab : QuotientGroup.rightRel localOmegaStabilizer a b) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal a x)) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal b x)) := by
  have hn : b * a⁻¹ ∈ localOmegaStabilizer := QuotientGroup.rightRel_apply.mp hab
  obtain ⟨h, hh⟩ := localOmegaStabilizer_triality_orbit ⟨b * a⁻¹, hn⟩ (rhoLocal a x)
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  refine ⟨h, ?_⟩
  rw [hh]
  apply congrArg sExtra
  rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel_right]

/-- The genuine finite transition domain acts on every actual representative. -/
noncomputable def generatedAxisGlobalDestination (x : GriessSpace) :
    generatedAxisTransitionCosetSpace → generatedAxisLocalOrbitSpace :=
  Quotient.lift (fun h : H =>
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal h x)))
    (generatedAxisGlobal_destination_congr x)

/-- The first source destination map is the specialization of the general map. -/
theorem generatedAxisGlobalDestination_first (p : Fin 276) :
    generatedAxisGlobalDestination (conwayAxis p) = generatedAxisTransitionDestination p := rfl

/-- Membership in a union of actual local orbits is exactly equality with one
of their genuine quotient classes. -/
theorem generatedAxisGlobal_mem_union_iff {ι : Type*} (v : ι → GriessSpace)
    (x : GriessSpace) :
    x ∈ generatedLocalOrbitUnion v ↔ ∃ i,
      Quotient.mk (MulAction.orbitRel H GriessSpace) x =
        Quotient.mk (MulAction.orbitRel H GriessSpace) (v i) := by
  constructor
  · rintro ⟨i, h, hh⟩
    refine ⟨i, (generatedAxis_local_class_eq_iff _ _).mpr ?_⟩
    refine ⟨h⁻¹, ?_⟩
    rw [← hh, rhoLocal.map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  · rintro ⟨i, he⟩
    obtain ⟨h, hh⟩ := (generatedAxis_local_class_eq_iff _ _).mp he.symm
    exact ⟨i, h, hh⟩

/-- Actual finite destination coverage, for every listed representative,
proves triality invariance of the entire local orbit union. -/
theorem generatedAxisGlobal_triality_of_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hcover : ∀ i c, ∃ j, generatedAxisGlobalDestination (v i) c =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (v j)) :
    Set.MapsTo sExtra (generatedLocalOrbitUnion v) (generatedLocalOrbitUnion v) := by
  rintro x ⟨i, h, rfl⟩
  apply (generatedAxisGlobal_mem_union_iff v _).mpr
  exact hcover i (Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
