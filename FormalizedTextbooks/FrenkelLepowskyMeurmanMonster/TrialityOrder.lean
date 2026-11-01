/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The order-three relation of the explicit dictionary triality.
Source: Seysen, arXiv:2002.10921v3, §8.3.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- XOR translation of the six free bits in an octad label. -/
def trialityXor (i j : Fin 64) : Fin 64 := ⟨(i.val ^^^ j.val) % 64, by omega⟩

/-- Binary characteristic function of the chosen even octad representative. -/
def trialityBinaryBit (i : Fin 64) (k : Fin 8) : ZMod 2 :=
  golayBooleanCast ((trialityEvenMask i).testBit k.val)

/-- The intersection pairing of even octad representatives. -/
def trialityBinaryPair (i j : Fin 64) : ZMod 2 :=
  ∑ k, trialityBinaryBit i k * trialityBinaryBit j k

/-- The two signs as integers, for exact Fourier computations. -/
def trialityIntegerSign (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

/-- The quadratic diagonal in the octad operation. -/
def trialityIntegerDiagonal (i : Fin 64) : ℤ :=
  if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then 1 else -1

theorem trialityIntegerSign_add (a b : ZMod 2) :
    trialityIntegerSign (a + b) = trialityIntegerSign a * trialityIntegerSign b := by
  revert a b
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed octad coordinates exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
/-- XOR of labels corresponds to XOR of the chosen even representatives. -/
theorem trialityEvenMask_xor : ∀ i j : Fin 64,
    trialityEvenMask (trialityXor i j) = trialityEvenMask i ^^^ trialityEvenMask j := by
  decide +kernel

/-- XOR of labels is addition of their binary even-subset representatives. -/
theorem trialityBinaryBit_xor (i j : Fin 64) (k : Fin 8) :
    trialityBinaryBit (trialityXor i j) k = trialityBinaryBit i k + trialityBinaryBit j k := by
  simp only [trialityBinaryBit, trialityEvenMask_xor, Nat.testBit_xor, golayBooleanCast_xor]

theorem trialityBinaryPair_xor (i j k : Fin 64) :
    trialityBinaryPair (trialityXor i j) k =
      trialityBinaryPair i k + trialityBinaryPair j k := by
  simp only [trialityBinaryPair, trialityBinaryBit_xor, add_mul, Finset.sum_add_distrib]

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed octad coordinates exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
/-- The source Hadamard entries are the signs of the binary pairing. -/
theorem trialityHadamard_binary : ∀ i j : Fin 64,
    trialityHadamard i j = trialityIntegerSign (trialityBinaryPair i j) := by
  unfold trialityHadamard trialityIntegerSign trialityBinaryPair
  decide +kernel

theorem trialityHadamard_xor (i j k : Fin 64) :
    trialityHadamard (trialityXor i j) k = trialityHadamard i k * trialityHadamard j k := by
  rw [trialityHadamard_binary, trialityBinaryPair_xor, trialityIntegerSign_add,
    ← trialityHadamard_binary, ← trialityHadamard_binary]

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed octad coordinates exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
/-- Polarization of the source quadratic octad signs. -/
theorem trialityIntegerDiagonal_xor : ∀ i j : Fin 64,
    trialityIntegerDiagonal (trialityXor i j) =
      trialityIntegerDiagonal i * trialityIntegerDiagonal j * trialityHadamard i j := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed octad coordinates exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
/-- The plus-type six-dimensional quadratic Gauss sum is eight. -/
theorem trialityIntegerDiagonal_fourier : ∀ i : Fin 64,
    (∑ k, trialityIntegerDiagonal k * trialityHadamard i k) =
      8 * trialityIntegerDiagonal i := by
  decide +kernel


/-- The unnormalized integer matrix of Fourier transform followed by signs. -/
def trialityIntegerMatrix : Matrix (Fin 64) (Fin 64) ℤ :=
  fun i j => trialityIntegerDiagonal i * trialityHadamard i j

@[simp] theorem trialityIntegerDiagonal_sq (i : Fin 64) :
    trialityIntegerDiagonal i * trialityIntegerDiagonal i = 1 := by
  simp only [trialityIntegerDiagonal]
  split <;> norm_num

theorem trialityHadamard_symmetric (i j : Fin 64) :
    trialityHadamard i j = trialityHadamard j i := by
  simp only [trialityHadamard, Nat.and_comm]

/-- Completing the square in the finite quadratic Gauss sum. -/
theorem trialityIntegerMatrix_square :
    trialityIntegerMatrix * trialityIntegerMatrix =
      8 • trialityIntegerMatrix.transpose := by
  ext i j
  simp only [Matrix.mul_apply, trialityIntegerMatrix, Matrix.transpose_apply,
    Matrix.smul_apply]
  have hh (k : Fin 64) :
      (trialityIntegerDiagonal i * trialityHadamard i k) *
        (trialityIntegerDiagonal k * trialityHadamard k j) =
      trialityIntegerDiagonal i *
        (trialityIntegerDiagonal k * trialityHadamard (trialityXor i j) k) := by
    rw [trialityHadamard_xor, trialityHadamard_symmetric k j]
    ring
  simp_rw [hh]
  rw [← Finset.mul_sum, trialityIntegerDiagonal_fourier, trialityIntegerDiagonal_xor]
  have hd := trialityIntegerDiagonal_sq i
  rw [trialityHadamard_symmetric j i]
  calc
    trialityIntegerDiagonal i *
      (8 * (trialityIntegerDiagonal i * trialityIntegerDiagonal j * trialityHadamard i j)) =
      8 * (trialityIntegerDiagonal i * trialityIntegerDiagonal i) *
        (trialityIntegerDiagonal j * trialityHadamard i j) := by ring
    _ = _ := by rw [hd]; ring

/-- The integer matrix is orthogonal up to the factor 64. -/
theorem trialityIntegerMatrix_mul_transpose :
    trialityIntegerMatrix * trialityIntegerMatrix.transpose =
      64 • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
  have ht : trialityHadamard.conjTranspose = trialityHadamard.transpose := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  have hh := triality_hadamard_isHadamard.mul_conjTranspose
  rw [ht] at hh
  ext i j
  simp only [Matrix.mul_apply, trialityIntegerMatrix, Matrix.transpose_apply,
    Matrix.smul_apply]
  have hf (k : Fin 64) :
      (trialityIntegerDiagonal i * trialityHadamard i k) *
        (trialityIntegerDiagonal j * trialityHadamard j k) =
      (trialityIntegerDiagonal i * trialityIntegerDiagonal j) *
        (trialityHadamard i k * trialityHadamard j k) := by ring
  simp_rw [hf]
  rw [← Finset.mul_sum]
  have hentry := congrArg (fun a : Matrix (Fin 64) (Fin 64) ℤ => a i j) hh
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.card_fin, Nat.cast_ofNat] at hentry
  rw [hentry]
  by_cases hij : i = j
  · subst j
    rw [trialityIntegerDiagonal_sq]
    simp
  · simp [hij]

/-- The integer cube is 512 times the identity, hence normalization gives order 3. -/
theorem trialityIntegerMatrix_cube :
    trialityIntegerMatrix * trialityIntegerMatrix * trialityIntegerMatrix =
      512 • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
  rw [Matrix.mul_assoc, trialityIntegerMatrix_square, Matrix.mul_smul,
    trialityIntegerMatrix_mul_transpose, smul_smul]
  norm_num

/-- The normalized real matrix of the actual octad operation. -/
noncomputable def trialityRealMatrix : Matrix (Fin 64) (Fin 64) ℝ :=
  (1 / 8 : ℝ) • trialityIntegerMatrix.map (Int.castRingHom ℝ)

/-- The normalized octad matrix has cube the identity. -/
theorem trialityRealMatrix_cube :
    trialityRealMatrix * trialityRealMatrix * trialityRealMatrix = 1 := by
  have hm : trialityIntegerMatrix.map (Int.castRingHom ℝ) *
      trialityIntegerMatrix.map (Int.castRingHom ℝ) *
      trialityIntegerMatrix.map (Int.castRingHom ℝ) =
      (512 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) := by
    change (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix *
      (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix *
      (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix = _
    rw [← map_mul, ← map_mul, trialityIntegerMatrix_cube]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.ofNat_apply, hij]
  simp only [trialityRealMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hm, smul_smul]
  norm_num

/-- Coordinate formula identifying the source operation with its real matrix. -/
theorem trialityOctadAction_matrix (x : Fin 64 → ℝ) :
    trialityOctadAction x = trialityRealMatrix.mulVec x := by
  funext i
  change (if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1) *
    (trialityNormalizedHadamard.mulVec x) i = _
  simp only [trialityNormalizedHadamard, trialityRealMatrix, Matrix.mulVec,
    dotProduct, Matrix.smul_apply, Matrix.map_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [trialityIntegerMatrix, map_mul]
  by_cases hi : trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0
  · simp only [trialityIntegerDiagonal, hi, ite_true, map_one]
    ring
  · simp only [trialityIntegerDiagonal, hi, ite_false, map_neg, map_one]
    ring

/-- Applying the actual octad triality three times gives the identity. -/
theorem trialityOctadAction_triple (x : Fin 64 → ℝ) :
    trialityOctadAction (trialityOctadAction (trialityOctadAction x)) = x := by
  rw [trialityOctadAction_matrix, trialityOctadAction_matrix, trialityOctadAction_matrix,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, trialityRealMatrix_cube, Matrix.one_mulVec]

theorem trialityCycle_symm_triple (i : Fin 3) :
    trialityCycle.symm (trialityCycle.symm (trialityCycle.symm i)) = i := by
  revert i
  decide +kernel

/-- The cyclic action on each three-block family has period three. -/
theorem trialityCycleAction_triple (n : ℕ) (x : Fin 3 → Fin n → ℝ) :
    trialityCycleAction n (trialityCycleAction n (trialityCycleAction n x)) = x := by
  ext i j
  simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply, trialityCycle_symm_triple]

/-- The entire dictionary action has period three. -/
theorem trialityBlockAction_triple (x : TrialityBlocks) :
    trialityBlockAction (trialityBlockAction (trialityBlockAction x)) = x := by
  simp only [trialityBlockAction, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    trialityCycleAction_triple]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  funext o
  exact trialityOctadAction_triple (x.2.2.1 o)

/-- Three applications of the extra Griess-space symmetry give the original vector. -/
theorem sExtra_triple (x : GriessSpace) : sExtra (sExtra (sExtra x)) = x := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact trialityBlockAction_triple (trialityBlocksEquiv x)

/-- The source order-three relation for the extra generator, without an algebra
invariance or Monster recognition hypothesis. -/
theorem sExtra_pow_three : sExtra ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  simpa only [pow_succ, pow_zero, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
    using sExtra_triple x
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
