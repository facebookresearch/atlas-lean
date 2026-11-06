/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsDefinitions

/-! The selected Q intersection is a genuine sixteen-element binary frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Four literal independent generators for the actual selected binary intersection. -/
def generatedFifthFrameSystemMatrix : Matrix (Fin 24) (Fin 4) (ZMod 2) :=
  fun i j => if (![2048, 458752, 2686976, 4194304] : Fin 4 → ℕ) j |>.testBit i.val
    then 1 else 0

/-- The sixteen binary coordinate vectors of the selected actual frame system. -/
def generatedFifthFrameSystemBinary : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  generatedFifthFrameSystemMatrix.mulVecLin.range

set_option maxHeartbeats 4000000 in
-- Verify the independence of four actual vectors on the sixteen binary inputs.
/-- The displayed four generators are linearly independent. -/
theorem generatedFifthFrameSystemMatrix_injective :
    Function.Injective generatedFifthFrameSystemMatrix.mulVecLin := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all sixteen input vectors against the fifteen actual nonzero frame classes.
/-- Every nonzero vector in this actual binary span is one of the fifteen incident classes. -/
theorem generatedFifthFrameSystemMatrix_nonzero : ∀ a : Fin 4 → ZMod 2,
    generatedFifthFrameSystemMatrix *ᵥ a ≠ 0 →
      ∃ j : Fin 15, generatedFifthFrameIncidentClass j =
        generatedFifthFrameSystemMatrix *ᵥ a := by
  decide +kernel

/-- The selected binary span has exactly sixteen elements. -/
theorem generatedFifthFrameSystemBinary_card : Nat.card generatedFifthFrameSystemBinary = 16 := by
  change Nat.card (Set.range generatedFifthFrameSystemMatrix.mulVecLin) = 16
  rw [← Nat.card_congr (Equiv.ofInjective generatedFifthFrameSystemMatrix.mulVecLin
    generatedFifthFrameSystemMatrix_injective)]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- The actual quotient subspace recovered from the displayed binary coordinate span. -/
def generatedFifthFrameSystem : Submodule (ZMod 2) LeechModTwo :=
  generatedFifthFrameSystemBinary.map leechHyperbolicCoordinates.symm.toLinearMap

/-- The actual quotient subspace has sixteen elements. -/
theorem generatedFifthFrameSystem_card : Nat.card generatedFifthFrameSystem = 16 := by
  rw [generatedFifthFrameSystem, ← Nat.card_congr
    (leechHyperbolicCoordinates.symm.submoduleMap generatedFifthFrameSystemBinary).toEquiv]
  exact generatedFifthFrameSystemBinary_card

/-- Every nonzero element is represented by a genuine norm-eight vector in the selected section. -/
theorem generatedFifthFrameSystem_incident (b : LeechModTwo)
    (hb : b ∈ generatedFifthFrameSystem) (hb0 : b ≠ 0) :
    b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  obtain ⟨v, ⟨a, ha⟩, hv⟩ := Submodule.mem_map.mp hb
  have hn : generatedFifthFrameSystemMatrix *ᵥ a ≠ 0 := by
    intro hz
    apply hb0
    rw [← hv, ← ha]
    simp only [Matrix.mulVecLin_apply, hz, map_zero]
  obtain ⟨j, hj⟩ := generatedFifthFrameSystemMatrix_nonzero a hn
  have he : b = leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass j) := by
    rw [← hv, ← ha]
    exact congrArg leechHyperbolicCoordinates.symm hj.symm
  rw [he]
  exact generatedFifthFrameIncidentClass_mem j

/-- The selected intersection is a genuine fifteen-frame system in the actual integral section. -/
theorem generatedFifthFrameSystem_mem : generatedFifthFrameSystem ∈
    generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) :=
  ⟨generatedFifthFrameSystem_card, generatedFifthFrameSystem_incident⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
