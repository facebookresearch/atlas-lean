/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSystemOrbit

/-! All genuine Golay signs preserve the original fifth system, and the original frame is Omega. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original encoder-basis sign preserves both genuine geometric objects. -/
theorem generatedFifthFrameSystem_basis_sign_mem (k : Fin 12) :
    monsterCo1GeometrySignIsometry k ∈ generatedFifthFrameSystemStabilizer := by
  rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem]
  refine ⟨generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ _), ?_⟩
  have h := generatedFifthFrameSignXi_system_preserved (⟨k.val, by omega⟩ : Fin 13)
  simpa [generatedFifthFrameSignXiIndex, generatedFifthSectionGenerator,
    monsterCo1GeometrySignIsometry, monsterCo1GeometrySignCode] using h

/-- Every genuine Golay codeword sign belongs to the full actual fifth-system stabilizer. -/
theorem generatedFifthFrameSystem_sign_mem (c : golayCode) :
    golaySignIsometry c ∈ generatedFifthFrameSystemStabilizer := by
  have h : monsterCo1GeometryBasisSignIsometrySubgroup ≤ generatedFifthFrameSystemStabilizer := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨k, rfl⟩
    exact generatedFifthFrameSystem_basis_sign_mem k
  exact h (monsterCo1Geometry_all_sign_mem c)

/-- The first original system class is the genuine distinguished coordinate-frame class. -/
theorem generatedFifthFrameClass_zero_base :
    generatedFifthFrameClass 0 = leechReduction (leechCoordinateFrameLattice 0) := by
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates
    (leechHyperbolicCoordinates.symm (generatedFifthFrameIncidentClass 0)) = _
  rw [LinearEquiv.apply_symm_apply, ← monsterCo1GeometryBasePoint_value,
    monsterCo1GeometryBasePoint_binary]
  decide +kernel

/-- Preserving the original first system class is exactly the actual monomial condition. -/
theorem generatedFifthFrameClass_zero_stabilizer :
    MulAction.stabilizer leechIsomSubgroup (generatedFifthFrameClass 0) =
      golayMonomialSubgroup := by
  rw [generatedFifthFrameClass_zero_base]
  exact leechFrameClass_stabilizer_eq_monomial

/-- An actual permutation preserves the full selected section exactly when it fixes its word. -/
theorem generatedFifthFrameSystem_permutation_mem (p : golayAutomorphismSubgroup) :
    golayPermutationIsometry p ∈ generatedFifthFrameSystemStabilizer ↔
      p ∈ generatedFifthSelectedOctadSubgroup ∧
        generatedFifthFrameSystem.map (leechModTwoAction (golayPermutationIsometry p)).toLinearMap =
          generatedFifthFrameSystem := by
  rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem,
    generatedAxisE8_permutation_image, generatedFifthSelectedOctadSubgroup_mem]
  exact and_congr (generatedAxisE8CoordinateSection_injective.eq_iff) Iff.rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
