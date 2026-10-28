/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSystemOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemStabilizer
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-! The displayed fifteen-system transitions are the actual lattice quotient action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Actual selected permutation actions on intrinsic root coordinates. -/
theorem generatedFifthSelectedOctad_binary (k : Fin 5) (a : Fin 8 → ZMod 2) :
    leechModTwoAction (golayPermutationHom (generatedFifthSelectedOctadPermutation k))
        (generatedAxisE8FrameRootEmbedding a) =
      generatedAxisE8FrameRootEmbedding
        (generatedFifthSectionGeneratorBinary ⟨12 + k.val, by omega⟩ *ᵥ a) := by
  have h12 : ¬12 + k.val < 12 := by omega
  have h17 : 12 + k.val < 17 := by omega
  simpa [generatedFifthSectionGenerator, golayPermutationHom, h12, h17] using
    generatedFifthSectionGenerator_binary (⟨12 + k.val, by omega⟩ : Fin 18) a

/-- Every forward intrinsic coefficient vector has its stated image. -/
theorem generatedFifthMonomialSystem_forward (k : Fin 5) (i : Fin 15)
    (a : Fin 4 → ZMod 2) :
    generatedFifthSectionGeneratorBinary ⟨12 + k.val, by omega⟩ *ᵥ
        generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i) a =
      generatedAxisE8FrameSystemCandidateMap
        (generatedFifthMonomialSystemIndex (generatedFifthMonomialSystemTransition k i))
        (generatedFifthMonomialSystemChange (generatedFifthMonomialSystemForward k i) *ᵥ a) := by
  change _ *ᵥ (generatedFifthMonomialSystemBasisMatrix i *ᵥ a) =
    generatedFifthMonomialSystemBasisMatrix (generatedFifthMonomialSystemTransition k i) *ᵥ _
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    generatedFifthMonomialSystem_forward_certificate]

/-- Every target intrinsic vector has a source, using the backward basis change. -/
theorem generatedFifthMonomialSystem_backward (k : Fin 5) (i : Fin 15)
    (a : Fin 4 → ZMod 2) :
    generatedFifthSectionGeneratorBinary ⟨12 + k.val, by omega⟩ *ᵥ
        generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i)
          (generatedFifthMonomialSystemChange (generatedFifthMonomialSystemBackward k i) *ᵥ a) =
      generatedAxisE8FrameSystemCandidateMap
        (generatedFifthMonomialSystemIndex (generatedFifthMonomialSystemTransition k i)) a := by
  change _ *ᵥ (generatedFifthMonomialSystemBasisMatrix i *ᵥ (_ *ᵥ a)) =
    generatedFifthMonomialSystemBasisMatrix (generatedFifthMonomialSystemTransition k i) *ᵥ a
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    generatedFifthMonomialSystem_backward_certificate]

/-- Pull back the genuine lattice quotient action along the original permutation homomorphism. -/
instance (priority := 2000) generatedFifthMonomialSystemMulAction :
    MulAction golayAutomorphismSubgroup (Submodule (ZMod 2) LeechModTwo) :=
  MulAction.compHom _ golayPermutationHom

/-- The displayed systems are actual subspaces in the original lattice quotient. -/
def generatedFifthMonomialSystem (i : Fin 15) : Submodule (ZMod 2) LeechModTwo :=
  generatedAxisE8ActualFrameSystemCandidate (generatedFifthMonomialSystemIndex i)

/-- Each displayed finite transition is exactly the actual action on an entire subspace. -/
theorem generatedFifthMonomialSystem_action (k : Fin 5) (i : Fin 15) :
    generatedFifthSelectedOctadPermutation k • generatedFifthMonomialSystem i =
      generatedFifthMonomialSystem (generatedFifthMonomialSystemTransition k i) := by
  ext b
  constructor
  · rintro ⟨v, ⟨u, ⟨a, rfl⟩, rfl⟩, rfl⟩
    let c := generatedFifthMonomialSystemChange (generatedFifthMonomialSystemForward k i) *ᵥ a
    refine Submodule.mem_map.mpr
      ⟨generatedAxisE8FrameSystemCandidateMap
        (generatedFifthMonomialSystemIndex (generatedFifthMonomialSystemTransition k i)) c,
        ⟨c, rfl⟩, ?_⟩
    change generatedAxisE8FrameRootEmbedding
        (generatedAxisE8FrameSystemCandidateMap
          (generatedFifthMonomialSystemIndex (generatedFifthMonomialSystemTransition k i)) c) =
      leechModTwoAction (golayPermutationHom (generatedFifthSelectedOctadPermutation k))
        (generatedAxisE8FrameRootEmbedding
          (generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i) a))
    rw [generatedFifthSelectedOctad_binary, generatedFifthMonomialSystem_forward]
  · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
    let c := generatedFifthMonomialSystemChange (generatedFifthMonomialSystemBackward k i) *ᵥ a
    refine Submodule.mem_map.mpr
      ⟨generatedAxisE8FrameRootEmbedding
        (generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i) c),
        Submodule.mem_map.mpr
          ⟨generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i) c,
            ⟨c, rfl⟩, rfl⟩, ?_⟩
    change leechModTwoAction (golayPermutationHom (generatedFifthSelectedOctadPermutation k))
        (generatedAxisE8FrameRootEmbedding
          (generatedAxisE8FrameSystemCandidateMap (generatedFifthMonomialSystemIndex i) c)) =
      generatedAxisE8FrameRootEmbedding
        (generatedAxisE8FrameSystemCandidateMap
          (generatedFifthMonomialSystemIndex (generatedFifthMonomialSystemTransition k i)) a)
    dsimp only [c]
    rw [generatedFifthSelectedOctad_binary, generatedFifthMonomialSystem_backward]

/-- The initial displayed system is the original fifth frame system. -/
theorem generatedFifthMonomialSystem_zero :
    generatedFifthMonomialSystem 0 = generatedFifthFrameSystem := by
  exact generatedFifthFrameSystem_actual_candidate.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
