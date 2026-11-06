/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary

/-! The two actual coordinate-zero-fixing source words and their complete
integer and binary lattice actions. Numerical permutation orders are not used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original Golay-automorphism words, retaining every stated source inverse. -/
def generatedAxisGlobalOddPermutation (k : Fin 2) : golayAutomorphismSubgroup :=
  (generatedAxisGlobalOddPermutationWords k).foldr
    (fun p a => (if p.2 then (omegaOrbitGolayPermutation p.1)⁻¹
      else omegaOrbitGolayPermutation p.1) * a) 1

set_option maxHeartbeats 2000000 in
-- Check every physical coordinate of both literal source words.
/-- The complete forward tables are exactly the actual source Golay permutations. -/
theorem generatedAxisGlobalOddPermutation_forward : ∀ k : Fin 2, ∀ i : Fin 24,
    (generatedAxisGlobalOddPermutation k).val i = generatedAxisGlobalOddPermutationForward k i := by
  decide +kernel

/-- Both original words fix the genuine distinguished coordinate. -/
theorem generatedAxisGlobalOddPermutation_zero (k : Fin 2) :
    (generatedAxisGlobalOddPermutation k).val 0 = 0 := by
  rw [generatedAxisGlobalOddPermutation_forward]
  fin_cases k <;> rfl

/-- Original physical coordinate matrices of the two literal permutations. -/
def generatedAxisGlobalOddPermutationPhysical (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if generatedAxisGlobalOddPermutationForward k j = i then 1 else 0

set_option maxHeartbeats 10000000 in
-- Verify both full integer lattice basis actions entry by entry.
/-- All 1152 cached integer entries satisfy the actual basis transport equations. -/
theorem generatedAxisGlobalOddPermutation_integral : ∀ k : Fin 2,
    generatedAxisGlobalOddPermutationPhysical k * leechBasisMatrix =
      leechBasisMatrix * generatedAxisGlobalOddPermutationIntegral k := by
  decide +kernel

/-- The source physical matrices act by the genuine coordinate permutations. -/
theorem generatedAxisGlobalOddPermutation_embedding (k : Fin 2) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalOddPermutation k)).val
      (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (generatedAxisGlobalOddPermutationPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24,
      generatedAxisGlobalOddPermutationPhysical k i j =
        if (generatedAxisGlobalOddPermutation k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold generatedAxisGlobalOddPermutationPhysical
    rw [← generatedAxisGlobalOddPermutation_forward]
    have he : (generatedAxisGlobalOddPermutation k).val j = i ↔
        (generatedAxisGlobalOddPermutation k).val.symm i = j := by
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- The cached integral basis action is the full actual lattice action. -/
theorem generatedAxisGlobalOddPermutation_basis (k : Fin 2) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalOddPermutation k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ
        (generatedAxisGlobalOddPermutationIntegral k *ᵥ u)) := by
  rw [generatedAxisGlobalOddPermutation_embedding, Matrix.mulVec_mulVec,
    generatedAxisGlobalOddPermutation_integral, ← Matrix.mulVec_mulVec]

/-- Binary matrices in the actual published hyperbolic coordinates. -/
def generatedAxisGlobalOddPermutationBinary (k : Fin 2) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  leechHyperbolicInverse *
    (generatedAxisGlobalOddPermutationIntegral k).map (Int.castRingHom (ZMod 2)) *
      leechHyperbolicMatrix

/-- The full binary matrices are the genuine Conway quotient action of the original words. -/
theorem generatedAxisGlobalOddPermutation_binary (k : Fin 2) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedAxisGlobalOddPermutation k))) v =
        generatedAxisGlobalOddPermutationBinary k *ᵥ v :=
  leechBinaryAction_of_basis_certificate _ _ (generatedAxisGlobalOddPermutation_basis k) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
