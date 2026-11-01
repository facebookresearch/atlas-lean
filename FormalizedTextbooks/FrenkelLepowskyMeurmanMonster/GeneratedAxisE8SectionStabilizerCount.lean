/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8OrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ProjectionRecognition

/-! Actual lattice-isometry section stabilizers and their exact order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine integral lattice maps act on actual integral submodules. -/
instance (priority := 2000) : MulAction leechIsomSubgroup (Submodule ℤ leechIntegral) where
  smul g S := generatedAxisE8SectionEquiv g S
  one_smul := generatedAxisE8SectionEquiv_one
  mul_smul := generatedAxisE8SectionEquiv_mul

/-- The group-action orbit is exactly the already counted actual image-section range. -/
theorem generatedAxisE8_section_action_orbit (c : Fin 24 → ZMod 2) :
    MulAction.orbit leechIsomSubgroup (generatedAxisE8CoordinateSection c) =
      generatedAxisE8SectionOrbit c := rfl

/-- The stabilizer of the genuine integral coordinate section inside actual Co0. -/
def generatedAxisE8SectionStabilizer (c : Fin 24 → ZMod 2) : Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup (generatedAxisE8CoordinateSection c)

/-- Stabilizer membership is genuine equality of the actual image submodule. -/
theorem generatedAxisE8SectionStabilizer_mem (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8SectionStabilizer c ↔
      generatedAxisE8ImageSection g c = generatedAxisE8CoordinateSection c := Iff.rfl

/-- The actual Co0 stabilizer of each coordinate E8 section has order 178362777600. -/
theorem generatedAxisE8_sectionStabilizer_card (o : Fin 759) :
    Nat.card (generatedAxisE8SectionStabilizer (golayOctadWord o)) = 178362777600 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let f : leechIsomSubgroup → MulAction.orbit leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord o)) :=
    fun g => ⟨g • generatedAxisE8CoordinateSection (golayOctadWord o), ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o))) := Finite.of_surjective f hf
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o)))
  let _ := Fintype.ofFinite (generatedAxisE8SectionStabilizer (golayOctadWord o))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o))
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedAxisE8_section_action_orbit, generatedAxisE8_sectionOrbit_card,
    co0_card_exact] at h
  change Nat.card (generatedAxisE8SectionStabilizer (golayOctadWord o)) = 178362777600
  change 46621575 * Nat.card (generatedAxisE8SectionStabilizer (golayOctadWord o)) =
    8315553613086720000 at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
