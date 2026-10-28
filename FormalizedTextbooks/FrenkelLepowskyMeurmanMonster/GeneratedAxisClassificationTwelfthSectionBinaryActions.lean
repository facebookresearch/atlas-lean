/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionBinaryData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary

/-! All24 genuine binary coordinates of every original selected-section generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete selected inverse coordinate cache is the actual original permutation inverse. -/
theorem generatedTwelfth_section_permutation_backward_actual (k : Fin 5) (i : Fin 24) :
    (generatedFifthSelectedOctadPermutation k).val.symm i =
      generatedTwelfthSectionPermutationBackward k i := by
  apply (generatedFifthSelectedOctadPermutation k).val.injective
  rw [Equiv.apply_symm_apply, generatedFifthSelectedOctad_forward,
    generatedTwelfth_section_permutation_inverse]

/-- Every original selected permutation has precisely its checked complete integral basis action. -/
theorem generatedTwelfth_section_permutation_basis (k : Fin 5) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedFifthSelectedOctadPermutation k)).val
        (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding
        (leechBasisMatrix *ᵥ (generatedTwelfthSectionPermutationIntegral k *ᵥ u)) := by
  change golayRealPermute (generatedFifthSelectedOctadPermutation k).val _ = _
  rw [golayRealPermute_embedding, Matrix.mulVec_mulVec,
    ← generatedTwelfth_section_permutation_integral_certificate]
  apply congrArg leechCoordinateEmbedding
  funext i
  change (leechBasisMatrix *ᵥ u) ((generatedFifthSelectedOctadPermutation k).val.symm i) = _
  rw [generatedTwelfth_section_permutation_backward_actual]
  rfl

/-- The actual original selected-permutation action on all24 lattice binary coordinates. -/
theorem generatedTwelfth_section_permutation_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (golayPermutationIsometry (generatedFifthSelectedOctadPermutation k)) v =
      (leechHyperbolicInverse *
        (generatedTwelfthSectionPermutationIntegral k).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ v :=
  leechBinaryAction_of_basis_certificate _ _ (generatedTwelfth_section_permutation_basis k) v

/-- Complete actual binary matrices of all eighteen signs, selected permutations and Xi. -/
def generatedTwelfthSectionBinaryMatrix (g : Fin 18) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if h : g.val < 12 then monsterCo1GeometrySignBinary ⟨g.val, h⟩
  else if h' : g.val < 17 then
    leechHyperbolicInverse *
      (generatedTwelfthSectionPermutationIntegral ⟨g.val - 12, by omega⟩).map
        (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix
  else leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
    leechHyperbolicMatrix

/-- All original selected-section generators act by their proved full lattice binary matrices. -/
theorem generatedTwelfth_section_generator_binary (g : Fin 18) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedFifthSectionGenerator g) v =
      generatedTwelfthSectionBinaryMatrix g *ᵥ v := by
  by_cases h : g.val < 12
  · simp only [generatedFifthSectionGenerator, generatedTwelfthSectionBinaryMatrix,
      h, dite_true]
    exact monsterCo1GeometrySign_binary ⟨g.val, h⟩ v
  · by_cases h' : g.val < 17
    · simp only [generatedFifthSectionGenerator, generatedTwelfthSectionBinaryMatrix,
        h, h', dite_false, dite_true]
      exact generatedTwelfth_section_permutation_binary ⟨g.val - 12, by omega⟩ v
    · have hg : g = 17 := Fin.ext (by omega)
      subst g
      exact co1Xi_binaryAction v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
