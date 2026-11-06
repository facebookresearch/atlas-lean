/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameOrbit

/-! Actual integral coordinate sections and their lattice-isometry orbit.
Frame incidence means an actual norm-eight lattice vector in the section,
not a proposed binary or abstract E8 label. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine integral sublattice supported on a coordinate codeword. -/
def generatedAxisE8CoordinateSection (c : Fin 24 → ZMod 2) : Submodule ℤ leechIntegral where
  carrier := {u | generatedOctadSupported c u.val}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro u v hu hv i hi
    change u.val i + v.val i = 0
    rw [hu i hi, hv i hi, zero_add]
  smul_mem' a u hu := by
    intro i hi
    change a * u.val i = 0
    rw [hu i hi, mul_zero]

/-- The actual image of an integral coordinate section under a lattice isometry. -/
noncomputable def generatedAxisE8ImageSection (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) : Submodule ℤ leechIntegral :=
  (generatedAxisE8CoordinateSection c).map (leechIntegralAction g).toLinearMap

/-- The actual section orbit, defined using the constructed lattice isometry action. -/
def generatedAxisE8SectionOrbit (c : Fin 24 → ZMod 2) : Set (Submodule ℤ leechIntegral) :=
  Set.range (fun g : leechIsomSubgroup => generatedAxisE8ImageSection g c)

/-- Actual frame classes incident with an integral section. -/
def generatedAxisE8FrameClasses (S : Submodule ℤ leechIntegral) : Set LeechModTwo :=
  {b | ∃ u : leechIntegral, u ∈ S ∧ leechSquareSum u.val = 64 ∧ leechReduction u = b}

/-- Image membership has the ordinary actual integral-vector witnesses. -/
theorem generatedAxisE8ImageSection_mem (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) (u : leechIntegral) :
    u ∈ generatedAxisE8ImageSection g c ↔
      ∃ v : leechIntegral, generatedOctadSupported c v.val ∧ leechIntegralAction g v = u :=
  Submodule.mem_map

/-- A support-preserving isometry fixes the entire actual integral section. -/
theorem generatedAxisE8_preserving_image (c : Fin 24 → ZMod 2) (g : leechIsomSubgroup)
    (hg : generatedOctadPreserves c g) :
    generatedAxisE8ImageSection g c = generatedAxisE8CoordinateSection c := by
  ext u
  rw [generatedAxisE8ImageSection, Submodule.mem_map_equiv]
  change generatedOctadSupported c ((leechIntegralAction g).symm u).val ↔
    generatedOctadSupported c u.val
  have h := hg ((leechIntegralAction g).symm u)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Composition on the actual section agrees with composition of the actual lattice maps. -/
theorem generatedAxisE8ImageSection_mul (g h : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) :
    generatedAxisE8ImageSection (g * h) c =
      (generatedAxisE8ImageSection h c).map (leechIntegralAction g).toLinearMap := by
  unfold generatedAxisE8ImageSection
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro u
  change leechIntegralAction (g * h) u = leechIntegralAction g (leechIntegralAction h u)
  rw [map_mul, LinearEquiv.mul_apply]

/-- An internal section-preserving factor changes no actual image section. -/
theorem generatedAxisE8ImageSection_mul_preserving (g h : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) (hh : generatedOctadPreserves c h) :
    generatedAxisE8ImageSection (g * h) c = generatedAxisE8ImageSection g c := by
  rw [generatedAxisE8ImageSection_mul, generatedAxisE8_preserving_image c h hh]
  rfl

/-- Every norm-eight vector in an actual section represents a frame class
in the already proved actual global frame orbit. -/
theorem generatedAxisE8FrameClasses_subset_frame_orbit (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) :
    generatedAxisE8FrameClasses (generatedAxisE8ImageSection g c) ⊆
      MulAction.orbit leechIsomSubgroup (leechReduction (leechCoordinateFrameLattice 0)) := by
  rintro b ⟨u, _, hu, rfl⟩
  obtain ⟨e, _, he⟩ := leechNormEight_concrete_transitive u hu
  have hframe : leechIntegralAction e u = leechCoordinateFrameLattice 0 := by
    apply Subtype.ext
    simpa only [leechCoordinateFrameLattice, leechCoordinateFrameVector] using he
  have h : leechModTwoAction e (leechReduction u) =
      leechReduction (leechCoordinateFrameLattice 0) := by
    change leechReduction (leechIntegralAction e u) = _
    rw [hframe]
  refine ⟨e⁻¹, ?_⟩
  change leechModTwoAction e⁻¹ (leechReduction (leechCoordinateFrameLattice 0)) = _
  rw [← h, map_inv]
  exact (leechModTwoAction e).symm_apply_apply _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
