/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitStabilizers

/-! The first feasible local orbit in Höhn–Seysen, arXiv:2508.01037, §4
and Table 3. The actual local stabilizer of the positive axis fixes the
opposite signed axis, so this orbit consists of one actual vector. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The opposite axis's actual orbit under the local positive-axis stabilizer. -/
noncomputable def generatedFeasibleLocalAnchorOrbit (p : Fin 276) : Set GriessSpace :=
  {x | ∃ h : localAxisStabilizer p,
    rhoLocal h.val (conwayShortAxis (Sum.inl (0, p)) 1) = x}

/-- The first feasible local orbit is genuinely the singleton opposite axis. -/
theorem generatedFeasibleLocalAnchorOrbit_eq_singleton (p : Fin 276) :
    generatedFeasibleLocalAnchorOrbit p = {conwayShortAxis (Sum.inl (0, p)) 1} := by
  ext x
  constructor
  · rintro ⟨h, hh⟩
    rw [localAxisStabilizer_signedAxis_fixed h.val p h.property 1] at hh
    exact Set.mem_singleton_iff.mpr hh.symm
  · intro hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    refine ⟨1, ?_⟩
    change rhoLocal 1 _ = _
    rw [map_one]
    rfl

/-- The source's feasible first-orbit anchor is exactly one, with no global count input. -/
theorem generatedFeasibleLocalAnchorOrbit_card (p : Fin 276) :
    Nat.card (generatedFeasibleLocalAnchorOrbit p) = 1 := by
  rw [generatedFeasibleLocalAnchorOrbit_eq_singleton]
  simp

/-- The singleton anchor is contained in the actual first-stabilizer orbit. -/
theorem generatedFeasibleLocalAnchorOrbit_subset (p : Fin 276) :
    generatedFeasibleLocalAnchorOrbit p ⊆ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, p)) 0) (conwayShortAxis (Sum.inl (0, p)) 1) := by
  rw [generatedFeasibleLocalAnchorOrbit_eq_singleton]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact MulAction.mem_orbit_self _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
