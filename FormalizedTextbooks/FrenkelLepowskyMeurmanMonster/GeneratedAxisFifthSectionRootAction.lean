/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootData

/-! The finite root matrices are actions of the original genuine lattice isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Twelve genuine Golay signs, five original selected permutations, and the original Xi. -/
def generatedFifthSectionGenerator (g : Fin 18) : leechIsomSubgroup :=
  if h : g.val < 12 then
    golaySignIsometry ⟨golayEncoder (Pi.single ⟨g.val, h⟩ 1), ⟨_, rfl⟩⟩
  else if h' : g.val < 17 then
    golayPermutationIsometry (generatedFifthSelectedOctadPermutation ⟨g.val - 12, by omega⟩)
  else co1XiIsometry

/-- The genuine integral root sum has the displayed integral lattice-basis coordinates. -/
theorem generatedFifthSection_root_sum_coordinates (a : Fin 8 → ℤ) :
    leechExplicitCoordinates (∑ j, a j • generatedFifthFrameRoot j) =
      generatedFifthFrameIntegerMatrix *ᵥ a := by
  rw [map_sum]
  simp only [map_smul, generatedFifthFrameRoot, LinearEquiv.apply_symm_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Every displayed root matrix is the actual integral action on the eight genuine lattice roots. -/
theorem generatedFifthSectionGenerator_root_image (g : Fin 18) (j : Fin 8) :
    leechIntegralAction (generatedFifthSectionGenerator g) (generatedFifthFrameRoot j) =
      ∑ k, (generatedFifthSectionGeneratorInteger g) k j • generatedFifthFrameRoot k := by
  by_cases h : g.val < 12
  · let k : Fin 12 := ⟨g.val, h⟩
    have hg : g = (⟨k.val, by omega⟩ : Fin 18) := rfl
    simp only [generatedFifthSectionGenerator, h, ↓reduceDIte]
    apply Subtype.ext
    rw [leechIntegralAction_golaySign, generatedFifthFrameRoot_physical]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [← generatedFifthFrame_insert_root_sum]
    exact funext (generatedFifthSectionGenerator_sign_certificate k j)
  · by_cases h' : g.val < 17
    · let k : Fin 5 := ⟨g.val - 12, by omega⟩
      have hg : g = (⟨12 + k.val, by omega⟩ : Fin 18) := Fin.ext (by dsimp [k]; omega)
      simp only [generatedFifthSectionGenerator, h, ↓reduceDIte, h']
      apply Subtype.ext
      rw [leechIntegralAction_golayPermutation, generatedFifthFrameRoot_physical]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [← generatedFifthFrame_insert_root_sum]
      change golayIntegerPermute (generatedFifthSelectedOctadPermutation k).val
          (generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j)) =
        generatedFifthFrameInsert (generatedOctadIntegerRootMatrix *ᵥ
          (generatedFifthSectionGeneratorInteger g).col j)
      funext i
      obtain ⟨a, rfl⟩ := (generatedFifthSelectedOctadPermutation k).val.surjective i
      simp only [golayIntegerPermute, Equiv.symm_apply_apply]
      rw [generatedFifthSelectedOctad_forward]
      have hC := congrArg generatedFifthSectionGeneratorInteger hg
      rw [hC]
      exact (generatedFifthSectionGenerator_permutation_certificate k j a).symm
    · have hg : g = 17 := Fin.ext (by omega)
      subst g
      change leechIntegralAction co1XiIsometry (generatedFifthFrameRoot j) = _
      apply leechExplicitCoordinates.injective
      rw [leechIntegralAction_coordinates_of_basis_certificate co1XiIsometry co1XiBasisMatrix
        (fun u => co1Xi_embedding_basis u), generatedFifthFrameRoot,
        LinearEquiv.apply_symm_apply, generatedFifthSectionGenerator_xi_certificate,
        generatedFifthSection_root_sum_coordinates]
      rfl

/-- Each coordinate basis vector is the quotient class of its genuine integral root. -/
theorem generatedFifthSection_root_embedding_basis (j : Fin 8) :
    generatedAxisE8FrameRootEmbedding (Pi.single j 1) =
      leechReduction (generatedFifthFrameRoot j) := by
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm
    (generatedFifthFrameBinaryMatrix *ᵥ Pi.single j 1)) = _
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one, generatedFifthFrameRoot_binary]

/-- The finite binary root columns are the original genuine quotient actions on the root basis. -/
theorem generatedFifthSectionGenerator_binary_basis (g : Fin 18) (j : Fin 8) :
    leechModTwoAction (generatedFifthSectionGenerator g)
        (generatedAxisE8FrameRootEmbedding (Pi.single j 1)) =
      generatedAxisE8FrameRootEmbedding
        (generatedFifthSectionGeneratorBinary g *ᵥ Pi.single j 1) := by
  rw [generatedFifthSection_root_embedding_basis, Matrix.mulVec_single_one]
  change leechReduction
      (leechIntegralAction (generatedFifthSectionGenerator g) (generatedFifthFrameRoot j)) =
    generatedAxisE8FrameRootEmbedding
      (fun i => ((generatedFifthSectionGeneratorInteger g) i j : ZMod 2))
  rw [generatedAxisE8FrameRootEmbedding_integer, generatedFifthSectionGenerator_root_image]

/-- The root-coordinate action agrees with the actual lattice quotient action. -/
theorem generatedFifthSectionGenerator_binary (g : Fin 18) (a : Fin 8 → ZMod 2) :
    leechModTwoAction (generatedFifthSectionGenerator g) (generatedAxisE8FrameRootEmbedding a) =
      generatedAxisE8FrameRootEmbedding (generatedFifthSectionGeneratorBinary g *ᵥ a) := by
  have h : (leechModTwoAction (generatedFifthSectionGenerator g)).toLinearMap.comp
      generatedAxisE8FrameRootEmbedding =
      generatedAxisE8FrameRootEmbedding.comp
        (generatedFifthSectionGeneratorBinary g).mulVecLin := by
    apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
    intro j
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe] using
      generatedFifthSectionGenerator_binary_basis g j
  exact LinearMap.congr_fun h a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
