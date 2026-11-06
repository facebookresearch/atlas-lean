/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionReturnCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCosets

/-! The actual destination map from transition cosets to actual local orbit classes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual local orbit classes of vectors under the faithful local representation. -/
abbrev generatedAxisLocalOrbitSpace := Quotient (MulAction.orbitRel H GriessSpace)

/-- Actual triality destinations have the same local orbit class on each genuine Ω coset. -/
theorem generatedAxisTransition_destination_congr (p : Fin 276) (a b : H)
    (hab : QuotientGroup.rightRel localOmegaStabilizer a b) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal a (conwayAxis p))) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra (rhoLocal b (conwayAxis p))) := by
  have hn : b * a⁻¹ ∈ localOmegaStabilizer :=
    QuotientGroup.rightRel_apply.mp hab
  obtain ⟨h, hh⟩ := localOmegaStabilizer_triality_orbit ⟨b * a⁻¹, hn⟩
    (rhoLocal a (conwayAxis p))
  have he : rhoLocal h (sExtra (rhoLocal a (conwayAxis p))) =
      sExtra (rhoLocal b (conwayAxis p)) := by
    rw [hh]
    apply congrArg sExtra
    change rhoLocal (b * a⁻¹) (rhoLocal a (conwayAxis p)) = rhoLocal b (conwayAxis p)
    rw [← LinearEquiv.mul_apply, ← rhoLocal.map_mul, inv_mul_cancel_right]
  apply Quotient.sound'
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit_symm.mp ⟨h, he⟩

/-- The genuine triality transition map takes actual cosets to actual local orbit classes. -/
noncomputable def generatedAxisTransitionDestination (p : Fin 276) :
    generatedAxisTransitionCosetSpace → generatedAxisLocalOrbitSpace :=
  Quotient.lift
    (fun h : H => Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal h (conwayAxis p))))
    (generatedAxisTransition_destination_congr p)

/-- The actual local action's starting orbit is the proved signed-short set. -/
theorem generatedAxisLocalActual_orbit_eq_signed (p : Fin 276) :
    MulAction.orbit H (conwayAxis p) = generatedSignedShortAxes := by
  rw [← conwayShortAxis_pair_zero p]
  exact generatedAxisLocalOrbit_eq_signed (Sum.inl (0, p)) 0

/-- The first destination fiber is exactly the previously counted returning cosets. -/
theorem generatedAxisTransitionDestination_first_fiber (p : Fin 276) :
    generatedAxisTransitionDestination p ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p)} =
        generatedAxisFirstReturnCosets p := by
  ext c
  constructor
  · intro hc
    induction c using Quotient.inductionOn with
    | h h =>
      have he : Quotient.mk (MulAction.orbitRel H GriessSpace)
          (sExtra (rhoLocal h (conwayAxis p))) =
            Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p) := hc
      have hh := MulAction.orbitRel_apply.mp (Quotient.exact' he)
      rw [generatedAxisLocalActual_orbit_eq_signed] at hh
      exact ⟨h, rfl, hh⟩
  · rintro ⟨h, rfl, hh⟩
    change Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal h (conwayAxis p))) =
        Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p)
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply, generatedAxisLocalActual_orbit_eq_signed]
    exact hh

/-- The actual transition map's first destination fiber has exactly 93,150 cosets. -/
theorem generatedAxisTransitionDestination_first_fiber_card (p : Fin 276) :
    Nat.card (generatedAxisTransitionDestination p ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p)}) = 93150 := by
  rw [generatedAxisTransitionDestination_first_fiber]
  exact generatedAxisFirstReturnCosets_card p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
