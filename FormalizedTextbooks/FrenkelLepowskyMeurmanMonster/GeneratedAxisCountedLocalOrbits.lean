/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddOrbitCount
public import Mathlib.GroupTheory.GroupAction.Blocks

/-! Four distinct counted actual local orbits inside the genuine global axis orbit.
This catalog does not assert coverage of the global orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual starting vectors for the four local orbits already counted. -/
def generatedCountedAxisRepresentative : Fin 4 → GriessSpace :=
  ![conwayShortAxis (Sum.inl (0, 0)) 0, generatedOctadLocalAxis 0 0,
    generatedOddAxis, generatedFourthAxis]

/-- The corresponding four genuine H orbits. -/
def generatedCountedAxisOrbit (i : Fin 4) : Set GriessSpace :=
  MulAction.orbit H (generatedCountedAxisRepresentative i)

/-- Exact orders of the four actual local orbits, with their literal vector bindings. -/
theorem generatedCountedAxisOrbit_card (i : Fin 4) :
    Nat.card (generatedCountedAxisOrbit i) =
      (![196560, 11935123200, 1630347264000, 1466587938816000] : Fin 4 → ℕ) i := by
  fin_cases i
  · exact generatedAxisLocalOrbit_card (Sum.inl (0, 0)) 0
  · exact generatedOctadLocalAxisOrbit_card 0 0
  · exact generatedOddLocalAxisOrbit_card
  · exact generatedFourthFlagFrames_axis_orbit_card

/-- The different proved cardinalities distinguish all four actual H orbits. -/
theorem generatedCountedAxisOrbit_injective : Function.Injective generatedCountedAxisOrbit := by
  intro i j h
  have hc := congrArg (fun s : Set GriessSpace => Nat.card s) h
  rw [generatedCountedAxisOrbit_card, generatedCountedAxisOrbit_card] at hc
  have hi : Function.Injective
      (![196560, 11935123200, 1630347264000, 1466587938816000] : Fin 4 → ℕ) := by
    decide +kernel
  exact hi hc

/-- The four counted actual local orbits are mutually disjoint. -/
theorem generatedCountedAxisOrbit_pairwise_disjoint :
    Pairwise (fun i j : Fin 4 => Disjoint (generatedCountedAxisOrbit i)
      (generatedCountedAxisOrbit j)) := by
  intro i j hij
  exact (MulAction.orbit.eq_or_disjoint (generatedCountedAxisRepresentative i)
    (generatedCountedAxisRepresentative j)).resolve_left
      (fun h => hij (generatedCountedAxisOrbit_injective h))

/-- Each literal counted representative lies in the actual global orbit. -/
theorem generatedCountedAxisRepresentative_mem_generated
    (i : Fin 4) (r : GriessShortIndex) (c : ZMod 2) :
    generatedCountedAxisRepresentative i ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  fin_cases i
  · exact generatedSignedShortAxes_subset_orbit r c ⟨((Sum.inl (0, 0)), 0), rfl⟩
  · exact generatedOctadLocalAxisOrbit_subset_generated 0 0 r c
      (MulAction.mem_orbit_self _)
  · exact generatedOddLocalAxisOrbit_subset_generated r c (MulAction.mem_orbit_self _)
  · exact generatedFourthAxis_mem_generatedOrbit r c

/-- Every vector in all four counted H orbits belongs to the actual global orbit. -/
theorem generatedCountedAxisOrbit_subset_generated
    (i : Fin 4) (r : GriessShortIndex) (c : ZMod 2) :
    generatedCountedAxisOrbit i ⊆ generatedVectorOrbit (conwayShortAxis r c) := by
  rintro x ⟨h, hh⟩
  obtain ⟨g, hg⟩ := generatedCountedAxisRepresentative_mem_generated i r c
  refine ⟨localIntoGenerated h * g, ?_⟩
  change rhoLocal h (g.val (conwayShortAxis r c)) = x
  rw [hg]
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
