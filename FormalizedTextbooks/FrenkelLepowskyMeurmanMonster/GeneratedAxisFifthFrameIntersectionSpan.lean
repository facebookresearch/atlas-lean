/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Transport

/-! Actual selected-section lattice vectors reduce into the displayed binary span. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer root matrix and actual inserted lattice roots have the same linear combinations. -/
theorem generatedFifthFrame_insert_root_sum (a : Fin 8 → ℤ) :
    generatedFifthFrameInsert (generatedOctadIntegerRootMatrix *ᵥ a) =
      ∑ j, a j • (generatedFifthFrameRoot j).val := by
  have hm : generatedOctadIntegerRootMatrix *ᵥ a =
      ∑ j, a j • generatedOctadIntegerRootMatrix.col j := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hm, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, generatedFifthFrameRoot_physical]

/-- Every actual selected-section lattice vector belongs to the integer span of the eight roots. -/
theorem generatedFifthFrame_integer_span (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    ∃ a : Fin 8 → ℤ, u = ∑ j, a j • generatedFifthFrameRoot j := by
  let a := generatedOctadIntegerRootCoordinates (generatedFifthFrameLocalCoordinates u)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have he := generatedFifthFrame_insert_root_sum a
  rw [generatedFifthFrame_local_reconstruction u hu, generatedFifthFrame_insert_local u hu] at he
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using he

/-- Every actual selected-section lattice class lies in the displayed binary root span. -/
theorem generatedFifthFrame_binary_span (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    leechHyperbolicCoordinates (leechReduction u) ∈ generatedFifthFrameBinarySpan := by
  obtain ⟨a, ha⟩ := generatedFifthFrame_integer_span u hu
  rw [ha, map_sum, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_zsmul, map_zsmul]
  exact generatedFifthFrameBinarySpan.toAddSubgroup.zsmul_mem
    (generatedFifthFrameRoot_mem_binarySpan j) (a j)

/-- Every genuine incident norm-eight frame class lies in the actual selected binary root span. -/
theorem generatedFifthFrame_incident_binary_span (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    leechHyperbolicCoordinates b ∈ generatedFifthFrameBinarySpan := by
  obtain ⟨u, hu, _, hub⟩ := hb
  rw [← hub]
  exact generatedFifthFrame_binary_span u hu

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
