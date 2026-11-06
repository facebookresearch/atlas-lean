/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFrameData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift

/-! The root-six projection frame is a genuine original Leech lattice isometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def permuteLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem permute_code (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) :
    golayPermute generatedAxisGlobalOddRoot06OctadPermutation c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (permuteLinear generatedAxisGlobalOddRoot06OctadPermutation).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  apply golayCode.smul_mem
  rw [show (permuteLinear generatedAxisGlobalOddRoot06OctadPermutation).comp golayEncoder
      (Pi.single j 1) = golayPermute generatedAxisGlobalOddRoot06OctadPermutation
        (golayEncoder (Pi.single j 1)) from rfl,
    generatedAxisGlobalOddRoot06OctadCode_certificate]
  exact ⟨_, rfl⟩

/-- The exact coordinate permutation is an actual Golay-code automorphism. -/
def generatedAxisGlobalOddRoot06OctadGolayPermutation : golayAutomorphismSubgroup :=
  ⟨generatedAxisGlobalOddRoot06OctadPermutation, by
    intro c
    constructor
    · exact permute_code c
    · intro hc
      have h := permute_code _ hc
      have hp : generatedAxisGlobalOddRoot06OctadPermutation *
          generatedAxisGlobalOddRoot06OctadPermutation = 1 := by
        apply Equiv.ext
        intro i
        change generatedAxisGlobalOddRoot06OctadPermArray
          (generatedAxisGlobalOddRoot06OctadPermArray i) = i
        exact generatedAxisGlobalOddRoot06OctadPerm_involution i
      rw [← golayPermute_mul, hp] at h
      exact h⟩

/-- The frame is a product of two genuine original Leech lattice isometries. -/
def generatedAxisGlobalOddRoot06OctadFrameIsometry : leechIsomSubgroup :=
  co1XiIsometry⁻¹ * golayPermutationIsometry generatedAxisGlobalOddRoot06OctadGolayPermutation

/-- Every frame matrix entry is the actual original lattice-isometry action on its coordinate basis. -/
theorem generatedAxisGlobalOddRoot06OctadFrame_actual :
    leechIsomMatrix generatedAxisGlobalOddRoot06OctadFrameIsometry =
      (generatedAxisGlobalOddRoot06OctadFrameQ).map (Rat.castHom ℝ) := by
  ext i j
  change ((co1XiMatrix * co1XiMatrix) *ᵥ
    (golayRealPermute generatedAxisGlobalOddRoot06OctadPermutation (Pi.single j 1))) i = _
  rw [co1XiMatrix_square_eq_transpose]
  have hp : golayRealPermute generatedAxisGlobalOddRoot06OctadPermutation
      (Pi.single j 1) = Pi.single (generatedAxisGlobalOddRoot06OctadPermutation j) 1 := by
    ext k
    simp only [golayRealPermute_apply, Pi.single_apply]
    simp only [show generatedAxisGlobalOddRoot06OctadPermutation.symm k = j ↔
      k = generatedAxisGlobalOddRoot06OctadPermutation j from
      (generatedAxisGlobalOddRoot06OctadPermutation.eq_symm_apply).symm]
  rw [hp, Matrix.mulVec_single]
  simp [co1XiMatrix, generatedAxisGlobalOddRoot06OctadFrameQ, Matrix.col,
    generatedAxisGlobalOddRoot06OctadPermutation]

/-- Sparse evaluation retains the complete physical matrix congruence. -/
theorem generatedAxisGlobalOddRoot06OctadMatrix_conjugation :
    generatedAxisGlobalOddRoot06OctadMatrixQ =
      generatedAxisGlobalOddRoot06OctadFrameQ *
        (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).1 *
          generatedAxisGlobalOddRoot06OctadFrameQ.transpose := by
  ext i j
  unfold generatedAxisGlobalOddRoot06OctadMatrixQ
  calc
    _ = ∑ k : Fin 24, ∑ l : Fin 24,
        generatedAxisGlobalOddRoot06OctadFrameQ i k *
          (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).1 k l *
          generatedAxisGlobalOddRoot06OctadFrameQ j l := by
      apply Finset.sum_congr rfl
      intro k _
      split_ifs with hk
      · simp only [hk, zero_mul, Finset.sum_const_zero]
      · apply Finset.sum_congr rfl
        intro l _
        split_ifs with hl
        · simp only [hl, mul_zero]
        · rfl
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]

/-- The complete standard frame remains a product of genuine original lattice isometries. -/
def generatedAxisGlobalOddRoot06OctadStandardFrameIsometry : leechIsomSubgroup :=
  golayPermutationIsometry generatedAxisGlobalOddRoot06OctadFinalGolayPermutation *
    generatedAxisGlobalOddRoot06OctadFrameIsometry

/-- Every entry of the complete standard frame is bound to its genuine original spatial action. -/
theorem generatedAxisGlobalOddRoot06OctadStandardFrame_actual :
    leechIsomMatrix generatedAxisGlobalOddRoot06OctadStandardFrameIsometry =
      generatedAxisGlobalOddRoot06OctadStandardFrameQ.map (Rat.castHom ℝ) := by
  ext i j
  change (golayRealPermute generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val
    (generatedAxisGlobalOddRoot06OctadFrameIsometry.val (Pi.single j 1))) i = _
  simp only [golayRealPermute_apply]
  have h := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ =>
    A (generatedAxisGlobalOddRoot06OctadFinalGolayPermutation.val.symm i) j)
      generatedAxisGlobalOddRoot06OctadFrame_actual
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
