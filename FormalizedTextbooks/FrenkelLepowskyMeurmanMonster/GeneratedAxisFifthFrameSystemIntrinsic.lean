/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionSystem
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCandidates

/-! The actual fifth frame system has its precise intrinsic E8 candidate coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic coordinates of the four already proved genuine fifth-system generators. -/
def generatedFifthFrameSystemIntrinsicMatrix : Matrix (Fin 8) (Fin 4) (ZMod 2) :=
  fun i j => if (![65, 54, 42, 7] : Fin 4 → ℕ) j |>.testBit i.val then 1 else 0

/-- The four-dimensional intrinsic subspace of the actual fifth system. -/
def generatedFifthFrameSystemIntrinsic : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  generatedFifthFrameSystemIntrinsicMatrix.mulVecLin.range

/-- The four intrinsic columns map to the original four actual quotient-coordinate columns. -/
theorem generatedFifthFrameSystem_intrinsic_matrix :
    generatedFifthFrameBinaryMatrix * generatedFifthFrameSystemIntrinsicMatrix =
      generatedFifthFrameSystemMatrix := by
  decide +kernel

/-- The intrinsic subspace maps to exactly the genuine selected fifth frame system. -/
theorem generatedFifthFrameSystem_intrinsic_image :
    generatedFifthFrameSystemIntrinsic.map generatedAxisE8FrameRootEmbedding =
      generatedFifthFrameSystem := by
  ext b
  constructor
  · rintro ⟨v, ⟨a, ha⟩, hv⟩
    refine Submodule.mem_map.mpr
      ⟨generatedFifthFrameSystemMatrix *ᵥ a, ⟨a, rfl⟩, ?_⟩
    rw [← hv, ← ha]
    change leechHyperbolicCoordinates.symm (generatedFifthFrameSystemMatrix *ᵥ a) =
      leechHyperbolicCoordinates.symm
        (generatedFifthFrameBinaryMatrix *ᵥ (generatedFifthFrameSystemIntrinsicMatrix *ᵥ a))
    rw [Matrix.mulVec_mulVec, generatedFifthFrameSystem_intrinsic_matrix]
  · rintro ⟨v, ⟨a, ha⟩, hv⟩
    refine Submodule.mem_map.mpr
      ⟨generatedFifthFrameSystemIntrinsicMatrix *ᵥ a, ⟨a, rfl⟩, ?_⟩
    rw [← hv, ← ha]
    change leechHyperbolicCoordinates.symm
        (generatedFifthFrameBinaryMatrix *ᵥ (generatedFifthFrameSystemIntrinsicMatrix *ᵥ a)) =
      leechHyperbolicCoordinates.symm (generatedFifthFrameSystemMatrix *ᵥ a)
    rw [Matrix.mulVec_mulVec, generatedFifthFrameSystem_intrinsic_matrix]

set_option maxRecDepth 10000 in
/-- Each actual fifth-system intrinsic vector lies in the precise four-space candidate14. -/
theorem generatedFifthFrameSystem_intrinsic_candidate_forward : ∀ a : Fin 4 → ZMod 2,
    ∃ b : Fin 4 → ZMod 2, generatedFifthFrameSystemIntrinsicMatrix *ᵥ a =
      generatedAxisE8FrameSystemCandidateMap 14 b := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Every vector of candidate14 belongs to the actual fifth-system intrinsic span. -/
theorem generatedFifthFrameSystem_intrinsic_candidate_backward : ∀ a : Fin 4 → ZMod 2,
    ∃ b : Fin 4 → ZMod 2, generatedAxisE8FrameSystemCandidateMap 14 a =
      generatedFifthFrameSystemIntrinsicMatrix *ᵥ b := by
  decide +kernel

/-- The actual fifth system has exactly the stated intrinsic candidate, with no label assumption. -/
theorem generatedFifthFrameSystem_intrinsic_candidate :
    generatedFifthFrameSystemIntrinsic = generatedAxisE8FrameSystemCandidate 14 := by
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := generatedFifthFrameSystem_intrinsic_candidate_forward a
    exact ⟨b, hb.symm⟩
  · rintro v ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := generatedFifthFrameSystem_intrinsic_candidate_backward a
    exact ⟨b, hb.symm⟩

/-- The genuine lattice-quotient fifth system is exactly its actual mapped candidate. -/
theorem generatedFifthFrameSystem_actual_candidate :
    generatedFifthFrameSystem = generatedAxisE8ActualFrameSystemCandidate 14 := by
  rw [← generatedFifthFrameSystem_intrinsic_image,
    generatedFifthFrameSystem_intrinsic_candidate]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
