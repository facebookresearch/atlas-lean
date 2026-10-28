/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthBinaryCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary

/-! The genuine binary actions of the fifth-axis stabilizer generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical permutation matrices act by the original genuine coordinate permutations. -/
theorem generatedAxisGlobalFifthPermutation_embedding (k : Fin 6) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)).val
      (leechCoordinateEmbedding u) =
    leechCoordinateEmbedding (generatedAxisGlobalFifthMonomialPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24,
      generatedAxisGlobalFifthMonomialPhysical k i j =
        if (generatedFifthMonomialSpatialPermutation k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold generatedAxisGlobalFifthMonomialPhysical
    rw [← generatedFifthMonomialSpatial_forward]
    have he : (generatedFifthMonomialSpatialPermutation k).val j = i ↔
        (generatedFifthMonomialSpatialPermutation k).val.symm i = j := by
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- Each checked integral matrix is the actual permutation action on the lattice basis. -/
theorem generatedAxisGlobalFifthPermutation_basis (k : Fin 6) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ
      (generatedAxisGlobalFifthMonomialIntegral k *ᵥ u)) := by
  rw [generatedAxisGlobalFifthPermutation_embedding, Matrix.mulVec_mulVec,
    generatedAxisGlobalFifthMonomial_integral_certificate, ← Matrix.mulVec_mulVec]

/-- Nineteen actual spatial generators: twelve signs, six permutations, and Xi. -/
def generatedAxisGlobalFifthSpatial (k : Fin 19) : leechIsomSubgroup :=
  if h : k.val < 12 then monsterCo1GeometrySignIsometry ⟨k.val, h⟩
  else if h' : k.val < 18 then
    golayPermutationIsometry (generatedFifthMonomialSpatialPermutation ⟨k.val - 12, by omega⟩)
  else co1XiIsometry

/-- Their binary matrices in the same genuine hyperbolic coordinates as Q. -/
def generatedAxisGlobalFifthBinaryMatrix (k : Fin 19) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if h : k.val < 12 then monsterCo1GeometrySignBinary ⟨k.val, h⟩
  else if h' : k.val < 18 then
    generatedAxisGlobalFifthPermutationBinary ⟨k.val - 12, by omega⟩
  else leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
    leechHyperbolicMatrix

/-- All nineteen matrices are the actual Conway quotient actions, rather than independent data. -/
theorem generatedAxisGlobalFifthSpatial_binary (k : Fin 19) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthSpatial k)) v =
      generatedAxisGlobalFifthBinaryMatrix k *ᵥ v := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalFifthSpatial, generatedAxisGlobalFifthBinaryMatrix,
      h, ↓reduceDIte]
    exact monsterCo1GeometrySign_binary _ _
  · by_cases h' : k.val < 18
    · simp only [generatedAxisGlobalFifthSpatial, generatedAxisGlobalFifthBinaryMatrix,
        h, h', ↓reduceDIte]
      change leechBinaryAction _ v = _
      rw [generatedAxisGlobalFifthPermutationBinary_certificate]
      exact leechBinaryAction_of_basis_certificate _ _
        (generatedAxisGlobalFifthPermutation_basis _) _
    · simp only [generatedAxisGlobalFifthSpatial, generatedAxisGlobalFifthBinaryMatrix,
        h, h', ↓reduceDIte]
      exact co1Xi_binaryAction v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
