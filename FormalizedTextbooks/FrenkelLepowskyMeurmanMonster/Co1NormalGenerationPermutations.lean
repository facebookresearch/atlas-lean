/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A concrete pure coordinate permutation in the normal closure of actual code signs. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fix the first two MOG columns and interchange consecutive pairs in the other four. -/
def co1PairSwap : Equiv.Perm (Fin 24) :=
  Equiv.swap 8 9 * Equiv.swap 10 11 * Equiv.swap 12 13 * Equiv.swap 14 15 *
    Equiv.swap 16 17 * Equiv.swap 18 19 * Equiv.swap 20 21 * Equiv.swap 22 23

/-- The pure integer permutation matrix. -/
def co1PairSwapMatrixZ : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if j = co1PairSwap i then 1 else 0

/-- Integer signs of the published codeword labelled 0x10. -/
def co1PairSwapSignZ (i : Fin 24) : ℤ := if (0xcccc00 : ℕ).testBit i.val then -1 else 1

/-- The integer diagonal matrix of the codeword sign used in the pair-swap word. -/
def co1PairSwapSignMatrixZ : Matrix (Fin 24) (Fin 24) ℤ := Matrix.diagonal co1PairSwapSignZ

set_option maxHeartbeats 4000000 in
-- Check the fixed code mask in all24 physical coordinates.
theorem co1PairSwapCode_bits : ∀ i : Fin 24,
    (sourceGeneratedSignCode 16).val i = if (0xcccc00 : ℕ).testBit i.val then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Integer arithmetic checks every entry of the conjugation word.
theorem co1PairSwap_integer_certificate :
    co1XiNumerator * co1PairSwapSignMatrixZ * co1XiNumerator.transpose =
      4 • co1PairSwapMatrixZ := by
  decide +kernel

/-- The real diagonal matrix obtained from the certified integer codeword sign. -/
noncomputable def co1PairSwapSignMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  co1PairSwapSignMatrixZ.map (Int.castRingHom ℝ)

/-- The real permutation matrix obtained from the certified integer pair swap. -/
noncomputable def co1PairSwapMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  co1PairSwapMatrixZ.map (Int.castRingHom ℝ)

/-- The actual code sign has the certified physical diagonal matrix. -/
theorem co1PairSwapSign_apply (x : Fin 24 → ℝ) :
    (golaySignIsometry (sourceGeneratedSignCode 16)).val x = co1PairSwapSignMatrix *ᵥ x := by
  funext i
  have hm : co1PairSwapSignMatrix = Matrix.diagonal (fun j => (co1PairSwapSignZ j : ℝ)) := by
    ext j k
    simp only [co1PairSwapSignMatrix, co1PairSwapSignMatrixZ,
      Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hm, Matrix.mulVec_diagonal]
  change qSign ((sourceGeneratedSignCode 16).val i) * x i = _
  rw [co1PairSwapCode_bits]
  unfold co1PairSwapSignZ
  split_ifs <;> simp [qSign_zero, qSign_one]

/-- Transport the exact integer certificate into the real coordinate action. -/
theorem co1PairSwap_real_certificate :
    co1XiMatrix * co1PairSwapSignMatrix * co1XiMatrix.transpose = co1PairSwapMatrix := by
  let M := co1XiNumerator.map (Int.castRingHom ℝ)
  have hX : co1XiMatrix = (1 / 2 : ℝ) • M := by
    ext i j
    simp [co1XiMatrix, co1XiMatrixQ, M]
    ring
  have hh := congrArg (Int.castRingHom ℝ).mapMatrix co1PairSwap_integer_certificate
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at hh
  have hr : ((4 : ℕ) • co1PairSwapMatrixZ).map (Int.castRingHom ℝ) =
      (4 : ℝ) • co1PairSwapMatrix := by
    ext i j
    change (((4 : ℕ) • co1PairSwapMatrixZ i j : ℤ) : ℝ) =
      (4 : ℝ) * (co1PairSwapMatrixZ i j : ℝ)
    simp
  rw [hr] at hh
  change M * co1PairSwapSignMatrix * M.transpose = (4 : ℝ) • co1PairSwapMatrix at hh
  rw [hX, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hh,
    smul_smul, smul_smul]
  norm_num

/-- The actual lattice word whose coordinate action is the pure pair-swap permutation. -/
noncomputable def co1PairSwapIsometry : leechIsomSubgroup :=
  co1XiIsometry * golaySignIsometry (sourceGeneratedSignCode 16) * co1XiIsometry⁻¹

theorem co1PairSwapIsometry_apply (x : Fin 24 → ℝ) :
    co1PairSwapIsometry.val x = fun i => x (co1PairSwap i) := by
  change co1XiMatrix *ᵥ
    ((golaySignIsometry (sourceGeneratedSignCode 16)).val (co1XiIsometry.val.symm x)) = _
  have hi : co1XiIsometry.val.symm x = co1XiMatrix.transpose *ᵥ x := by
    change (co1XiMatrix * co1XiMatrix) *ᵥ x = _
    rw [co1XiMatrix_square_eq_transpose]
  rw [hi, co1PairSwapSign_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    co1PairSwap_real_certificate]
  funext i
  simp [co1PairSwapMatrix, co1PairSwapMatrixZ, Matrix.mulVec, dotProduct]

/-- Every actual normal subgroup containing the code sign contains this actual permutation word. -/
theorem co1PairSwapIsometry_mem_of_sign_mem (K : Subgroup ↥leechIsomSubgroup) [hK : K.Normal]
    (hs : golaySignIsometry (sourceGeneratedSignCode 16) ∈ K) : co1PairSwapIsometry ∈ K :=
  hK.conj_mem _ hs co1XiIsometry

/-- The same pure permutation class belongs to the normal closure of the code sign in Co₁. -/
theorem co1PairSwapClass_mem_of_signClass_mem (K : Subgroup Co1) [K.Normal]
    (hs : (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode 16)) : Co1) ∈ K) :
    (QuotientGroup.mk co1PairSwapIsometry : Co1) ∈ K :=
  co1PairSwapIsometry_mem_of_sign_mem (K.comap (QuotientGroup.mk' signsSubgroup)) hs

/-- This actual permutation is an involution. -/
theorem co1PairSwap_inverse : co1PairSwap⁻¹ = co1PairSwap := by
  apply Equiv.ext
  have h : ∀ i : Fin 24, co1PairSwap⁻¹ i = co1PairSwap i := by decide +kernel
  exact h

/-- Image labels of the twelve published generator rows under the pure pair swaps. -/
def co1PairSwapCodeImages : Fin 12 → Fin 4096 :=
  ![1, 2, 4, 8, 16, 47, 76, 134, 268, 522, 1055, 2048]

set_option maxHeartbeats 2000000 in
-- The twelve generator images certify the actual code-preservation calculation.
theorem co1PairSwap_generator_certificate : ∀ j : Fin 12,
    golayPermute co1PairSwap (golayEncoder (Pi.single j 1)) =
      golayEncoder (golayLabelCoefficients (co1PairSwapCodeImages j)) := by
  decide +kernel

private def co1PairSwapLinear : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute co1PairSwap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem co1PairSwap_code_mem (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) :
    golayPermute co1PairSwap c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change co1PairSwapLinear.comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  apply golayCode.smul_mem
  change golayPermute co1PairSwap (golayEncoder (Pi.single j 1)) ∈ golayCode
  rw [co1PairSwap_generator_certificate]
  exact ⟨_, rfl⟩

/-- The matrix word is a genuine element of the actual Golay permutation subgroup. -/
def co1PairSwapGolay : golayAutomorphismSubgroup :=
  ⟨co1PairSwap, by
    intro c
    constructor
    · exact co1PairSwap_code_mem c
    · intro hc
      have hh : golayPermute co1PairSwap⁻¹ (golayPermute co1PairSwap c) ∈ golayCode := by
        rw [co1PairSwap_inverse]
        exact co1PairSwap_code_mem _ hc
      rw [golayPermute_inv] at hh
      exact hh⟩

/-- Equality of the source ξ/sign word with the genuine Golay-permutation isometry. -/
theorem co1PairSwapIsometry_eq_golayPermutation :
    co1PairSwapIsometry = golayPermutationIsometry co1PairSwapGolay := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [co1PairSwapIsometry_apply]
  funext i
  change x (co1PairSwap i) = x (co1PairSwap⁻¹ i)
  rw [co1PairSwap_inverse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
