/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions

/-! One-xi coset representatives for the Fifth forest roots 0, 1, 6 and 12.

Each representative is a literal local word with a single original Xi factor. Its actual binary
root is computed from the original binary operators, and an explicit product of genuine full
Fifth-axis fixers carries the binary root of the forest root word to it. Hence both triality images
at the forest root follow from both triality images at the representative
(`generatedAxisGlobalTwelve_root_pair_mem`). The triality images at the representatives are not
bound here: the transfer lemmas take them as explicit hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The binary inverse of the first original source permutation operator. -/
def generatedAxisGlobalTwelveFifthBindPermutationZeroInverse :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
  ![0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
  ![0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1],
  ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

private theorem xiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem permutationZeroBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

private theorem permutationOneBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1) v = omegaOrbitBinaryMatrices 4 *ᵥ v :=
  omegaOrbitIsometry_binary 4 v

set_option maxHeartbeats 1000000 in
-- One complete 24 by 24 binary matrix product.
/-- The displayed matrix inverts the binary action of the first source permutation. -/
theorem generatedAxisGlobalTwelveFifthBindPermutationZeroInverse_mul :
    omegaOrbitBinaryMatrices 3 * generatedAxisGlobalTwelveFifthBindPermutationZeroInverse = 1 := by
  decide +kernel

/-- The inverse first source permutation acts on Λ/2Λ by the displayed inverse matrix. -/
theorem generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0)⁻¹ v =
      generatedAxisGlobalTwelveFifthBindPermutationZeroInverse *ᵥ v := by
  have h1 : leechBinaryAction (omegaOrbitPermutationIsometry 0)
      (generatedAxisGlobalTwelveFifthBindPermutationZeroInverse *ᵥ v) = v := by
    rw [permutationZeroBinary, Matrix.mulVec_mulVec,
      generatedAxisGlobalTwelveFifthBindPermutationZeroInverse_mul, Matrix.one_mulVec]
  calc leechBinaryAction (omegaOrbitPermutationIsometry 0)⁻¹ v =
      leechBinaryAction (omegaOrbitPermutationIsometry 0)⁻¹
        (leechBinaryAction (omegaOrbitPermutationIsometry 0)
          (generatedAxisGlobalTwelveFifthBindPermutationZeroInverse *ᵥ v)) := by rw [h1]
    _ = _ := by rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The one-xi representative word of each of the Fifth roots 0, 1, 6 and 12 (in this order). -/
def generatedAxisGlobalTwelveFifthBindCosetFiber : Fin 4 → localFiberSubgroup :=
  ![xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 1)⁻¹,
    xiSpinLocalFiber⁻¹ * monsterSourcePermutationFiber 0 * (monsterSourcePermutationFiber 1)⁻¹ *
      (monsterSourcePermutationFiber 0)⁻¹ * (monsterSourcePermutationFiber 1)⁻¹,
    xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 1)⁻¹ * (monsterSourcePermutationFiber 0)⁻¹,
    xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 0)⁻¹]

/-- The corresponding local representatives. -/
def generatedAxisGlobalTwelveFifthBindCoset (k : Fin 4) : H :=
  localFiberIntoH (generatedAxisGlobalTwelveFifthBindCosetFiber k)

/-- The Fifth forest roots represented, in the same order. -/
def generatedAxisGlobalTwelveFifthBindCosetRoot : Fin 4 → Fin 14 := ![0, 1, 6, 12]

/-- The exact binary roots of the four representatives. -/
def generatedAxisGlobalTwelveFifthBindCosetMask : Fin 4 → ℕ :=
  ![4243456, 7385088, 7344128, 5181440]

/-- The inverse representative words have these original spatial parts. -/
theorem generatedAxisGlobalTwelveFifthBindCoset_inv_spatial :
    (generatedAxisGlobalTwelveFifthBindCosetFiber 0)⁻¹.val.2 =
        omegaOrbitPermutationIsometry 1 * co1XiIsometry ∧
      (generatedAxisGlobalTwelveFifthBindCosetFiber 1)⁻¹.val.2 =
        omegaOrbitPermutationIsometry 1 * omegaOrbitPermutationIsometry 0 *
          omegaOrbitPermutationIsometry 1 * (omegaOrbitPermutationIsometry 0)⁻¹ * co1XiIsometry ∧
      (generatedAxisGlobalTwelveFifthBindCosetFiber 2)⁻¹.val.2 =
        omegaOrbitPermutationIsometry 0 * omegaOrbitPermutationIsometry 1 * co1XiIsometry ∧
      (generatedAxisGlobalTwelveFifthBindCosetFiber 3)⁻¹.val.2 =
        omegaOrbitPermutationIsometry 0 * co1XiIsometry := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (generatedAxisGlobalTwelveFifthBindCosetFiber 0)⁻¹.val.2 =
        (co1XiIsometry⁻¹ * (omegaOrbitPermutationIsometry 1)⁻¹)⁻¹ := rfl
    rw [h]; group
  · have h : (generatedAxisGlobalTwelveFifthBindCosetFiber 1)⁻¹.val.2 =
        (co1XiIsometry⁻¹ * omegaOrbitPermutationIsometry 0 * (omegaOrbitPermutationIsometry 1)⁻¹ *
          (omegaOrbitPermutationIsometry 0)⁻¹ * (omegaOrbitPermutationIsometry 1)⁻¹)⁻¹ := rfl
    rw [h]; group
  · have h : (generatedAxisGlobalTwelveFifthBindCosetFiber 2)⁻¹.val.2 =
        (co1XiIsometry⁻¹ * (omegaOrbitPermutationIsometry 1)⁻¹ *
          (omegaOrbitPermutationIsometry 0)⁻¹)⁻¹ := rfl
    rw [h]; group
  · have h : (generatedAxisGlobalTwelveFifthBindCosetFiber 3)⁻¹.val.2 =
        (co1XiIsometry⁻¹ * (omegaOrbitPermutationIsometry 0)⁻¹)⁻¹ := rfl
    rw [h]; group

private theorem binaryRoot_val (f : localFiberSubgroup) :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH f)).val =
      leechBinaryAction f⁻¹.val.2 (toAdd (qQuotHom sourceOmegaQ)) := by
  change co1BinaryAction (projH (localFiberIntoH f)⁻¹) (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← map_inv]
  rfl

set_option maxHeartbeats 20000000 in
-- Four short products of original binary operators on the complete 24-coordinate point.
/-- Every representative has exactly its displayed binary root. -/
theorem generatedAxisGlobalTwelveFifthBindCoset_root (k : Fin 4) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFifthBindCoset k)).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFifthBindCosetMask k) := by
  obtain ⟨h0, h1, h2, h3⟩ := generatedAxisGlobalTwelveFifthBindCoset_inv_spatial
  unfold generatedAxisGlobalTwelveFifthBindCoset
  rw [binaryRoot_val]
  fin_cases k
  · change leechBinaryAction (generatedAxisGlobalTwelveFifthBindCosetFiber 0)⁻¹.val.2 _ = _
    rw [h0]
    simp only [map_mul, LinearEquiv.mul_apply]
    simp_rw [xiBinary, permutationOneBinary]
    decide +kernel
  · change leechBinaryAction (generatedAxisGlobalTwelveFifthBindCosetFiber 1)⁻¹.val.2 _ = _
    rw [h1]
    simp only [map_mul, LinearEquiv.mul_apply]
    simp_rw [xiBinary, permutationZeroBinary, permutationOneBinary,
      generatedAxisGlobalTwelveFifthBind_permutationZeroInverse_binary]
    decide +kernel
  · change leechBinaryAction (generatedAxisGlobalTwelveFifthBindCosetFiber 2)⁻¹.val.2 _ = _
    rw [h2]
    simp only [map_mul, LinearEquiv.mul_apply]
    simp_rw [xiBinary, permutationZeroBinary, permutationOneBinary]
    decide +kernel
  · change leechBinaryAction (generatedAxisGlobalTwelveFifthBindCosetFiber 3)⁻¹.val.2 _ = _
    rw [h3]
    simp only [map_mul, LinearEquiv.mul_apply]
    simp_rw [xiBinary, permutationZeroBinary]
    decide +kernel

/-- Genuine full Fifth-axis fixers transporting each forest root to its representative. -/
def generatedAxisGlobalTwelveFifthBindCosetTransport : Fin 4 → generatedFifthLocalAxisStabilizer :=
  ![generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 17 *
      generatedAxisGlobalFifthGenerator 16 * generatedAxisGlobalFifthGenerator 16,
    generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 14 *
      generatedAxisGlobalFifthGenerator 4,
    generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 17 *
      generatedAxisGlobalFifthGenerator 10 * generatedAxisGlobalFifthGenerator 13 *
      generatedAxisGlobalFifthGenerator 0,
    generatedAxisGlobalFifthGenerator 15 * generatedAxisGlobalFifthGenerator 18 *
      generatedAxisGlobalFifthGenerator 6]

set_option maxHeartbeats 20000000 in
-- Short products of the actual generator binary matrices on four complete binary points.
/-- Each transport carries the binary root of the forest root word to the representative's. -/
theorem generatedAxisGlobalTwelveFifthBindCosetTransport_actual (k : Fin 4) :
    generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFifthBindCosetTransport k).val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalTwelveFifthBindCosetRoot k))) =
        generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveFifthBindCoset k) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindCoset_root]
  fin_cases k
  · change (generatedAxisGlobalBinaryAct
      ((generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 17).val *
        (generatedAxisGlobalFifthGenerator 16).val * (generatedAxisGlobalFifthGenerator 16).val)
      (generatedAxisGlobalFifthRoot 0)).val = _
    simp only [generatedAxisGlobalBinaryAct_mul]
    simp_rw [generatedAxisGlobalFifthGenerator_binary]
    decide +kernel
  · change (generatedAxisGlobalBinaryAct
      ((generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 14).val *
        (generatedAxisGlobalFifthGenerator 4).val) (generatedAxisGlobalFifthRoot 1)).val = _
    simp only [generatedAxisGlobalBinaryAct_mul]
    simp_rw [generatedAxisGlobalFifthGenerator_binary]
    decide +kernel
  · change (generatedAxisGlobalBinaryAct
      ((generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 17).val *
        (generatedAxisGlobalFifthGenerator 10).val * (generatedAxisGlobalFifthGenerator 13).val *
        (generatedAxisGlobalFifthGenerator 0).val) (generatedAxisGlobalFifthRoot 6)).val = _
    simp only [generatedAxisGlobalBinaryAct_mul]
    simp_rw [generatedAxisGlobalFifthGenerator_binary]
    decide +kernel
  · change (generatedAxisGlobalBinaryAct
      ((generatedAxisGlobalFifthGenerator 15).val * (generatedAxisGlobalFifthGenerator 18).val *
        (generatedAxisGlobalFifthGenerator 6).val) (generatedAxisGlobalFifthRoot 12)).val = _
    simp only [generatedAxisGlobalBinaryAct_mul]
    simp_rw [generatedAxisGlobalFifthGenerator_binary]
    decide +kernel

/-- Transfer: both triality images at a representative give both images at its forest root.
The images at the representative are hypotheses here. -/
theorem generatedAxisGlobalTwelveFifthBindCoset_transfer (k : Fin 4)
    (hpos : sExtra (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset k) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset k) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalTwelveFifthBindCosetRoot k)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalTwelveFifthBindCosetRoot k)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_root_pair_mem _ generatedFifthAxis
    (generatedAxisGlobalTwelveFifthBindCoset k)
    (generatedAxisGlobalFifthShortLocalWord (generatedAxisGlobalTwelveFifthBindCosetRoot k))
    (generatedAxisGlobalTwelveFifthBindCosetTransport k).val
    (generatedAxisGlobalTwelveFifthBindCosetTransport k).property
    (generatedAxisGlobalTwelveFifthBindCosetTransport_actual k) hpos hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
