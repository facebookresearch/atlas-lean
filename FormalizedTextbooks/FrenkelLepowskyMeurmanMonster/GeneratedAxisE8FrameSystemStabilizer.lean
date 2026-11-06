/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsDefinitions

/-! Actual simultaneous stabilizers of an integral E8 section and an entire binary frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original lattice quotient action transports whole actual binary subspaces. -/
instance (priority := 2000) generatedAxisE8FrameSystemMulAction :
    MulAction leechIsomSubgroup (Submodule (ZMod 2) LeechModTwo) where
  smul g W := W.map (leechModTwoAction g).toLinearMap
  one_smul W := by
    change W.map (leechModTwoAction 1).toLinearMap = W
    rw [map_one]
    exact Submodule.map_id W
  mul_smul g h W := by
    change W.map (leechModTwoAction (g * h)).toLinearMap =
      (W.map (leechModTwoAction h).toLinearMap).map (leechModTwoAction g).toLinearMap
    rw [map_mul]
    change W.map ((leechModTwoAction g).toLinearMap.comp (leechModTwoAction h).toLinearMap) =
      (W.map (leechModTwoAction h).toLinearMap).map (leechModTwoAction g).toLinearMap
    exact Submodule.map_comp _ _ W

/-- The full original Co0 stabilizer of the actual section and the entire actual binary subspace. -/
def generatedAxisE8FrameSystemStabilizer (o : Fin 759) (W : Submodule (ZMod 2) LeechModTwo) :
    Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup
    (generatedAxisE8CoordinateSection (golayOctadWord o), W)

/-- Membership fixes both actual geometric objects, rather than a chosen label or vector. -/
theorem generatedAxisE8FrameSystemStabilizer_mem (o : Fin 759)
    (W : Submodule (ZMod 2) LeechModTwo) (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8FrameSystemStabilizer o W ↔
      generatedAxisE8ImageSection g (golayOctadWord o) =
        generatedAxisE8CoordinateSection (golayOctadWord o) ∧
      W.map (leechModTwoAction g).toLinearMap = W := Prod.ext_iff

/-- Both original central lattice signs act trivially on every actual binary frame system. -/
theorem generatedAxisE8FrameSystemStabilizer_signs_le (o : Fin 759)
    (W : Submodule (ZMod 2) LeechModTwo) :
    signsSubgroup ≤ generatedAxisE8FrameSystemStabilizer o W := by
  intro g hg
  rw [generatedAxisE8FrameSystemStabilizer_mem]
  refine ⟨(generatedAxisE8SectionStabilizer_mem _ g).mp
    (generatedAxisE8_signs_le_section_stabilizer _ hg), ?_⟩
  have he : leechModTwoAction g = 1 := by
    ext b
    apply leechHyperbolicCoordinates.injective
    rw [← leechBinaryAction_coordinates, leechBinaryAction_sign g hg]
    rfl
  rw [he]
  exact Submodule.map_id W

/-- The actual simultaneous stabilizer in the original quotient by the two central signs. -/
def generatedAxisE8FrameSystemCo1Stabilizer (o : Fin 759)
    (W : Submodule (ZMod 2) LeechModTwo) : Subgroup Co1 :=
  (generatedAxisE8FrameSystemStabilizer o W).map (QuotientGroup.mk' signsSubgroup)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
