/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Fourier intertwinings of the actual local octad pair actions.
Small coefficient checks identify the pair translation and its character;
all 64-dimensional matrix identities then follow from Fourier polarization.
Source: Seysen, §8.1, equations (8.1.1)–(8.1.4).
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The coordinate-pair character on the normalized even octad representatives. -/
def trialityOctadPairSign (a b : Fin 8) (e : Fin 64) : ℤ :=
  (if (trialityEvenMask e).testBit a.val then -1 else 1) *
    (if (trialityEvenMask e).testBit b.val then -1 else 1)

/-- The six-bit translation representing the normalized pair flip. -/
def trialityOctadPairShift (a b : Fin 8) : Fin 64 := trialityOctadPairFlip a b 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check only the 8×8×64 local flip coefficients, not matrix products.
theorem trialityOctadPairFlip_xor : ∀ a b : Fin 8, ∀ e : Fin 64,
    trialityOctadPairFlip a b e = trialityXor e (trialityOctadPairShift a b) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Pair translations have quadratic sign minus one; only the 56 ordered pairs.
theorem trialityOctadPairShift_diagonal : ∀ a b : Fin 8, a ≠ b →
    trialityIntegerDiagonal (trialityOctadPairShift a b) = -1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Identify the 8×8×64 local Fourier character coefficients.
theorem trialityOctadPairShift_hadamard : ∀ a b : Fin 8, a ≠ b → ∀ e : Fin 64,
    trialityHadamard (trialityOctadPairShift a b) e = trialityOctadPairSign a b e := by
  decide +kernel

@[simp] theorem trialityOctadPairSign_sq (a b : Fin 8) (e : Fin 64) :
    trialityOctadPairSign a b e * trialityOctadPairSign a b e = 1 := by
  unfold trialityOctadPairSign
  split_ifs <;> norm_num

/-- The normalized pair flip is an involution. -/
theorem trialityOctadPairFlip_involutive (a b : Fin 8) :
    Function.Involutive (trialityOctadPairFlip a b) := by
  intro e
  rw [trialityOctadPairFlip_xor, trialityOctadPairFlip_xor]
  apply Fin.ext
  change (((e.val ^^^ (trialityOctadPairShift a b).val) % 64) ^^^
    (trialityOctadPairShift a b).val) % 64 = e.val
  have hx : e.val ^^^ (trialityOctadPairShift a b).val < 64 := by
    exact Nat.xor_lt_two_pow (n := 6) e.isLt (trialityOctadPairShift a b).isLt
  rw [Nat.mod_eq_of_lt hx, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
    Nat.mod_eq_of_lt e.isLt]

/-- Column translation is the pair character on each Fourier row. -/
theorem trialityIntegerMatrix_pair_flip_column (a b : Fin 8) (hab : a ≠ b)
    (e f : Fin 64) :
    trialityIntegerMatrix e (trialityOctadPairFlip a b f) =
      trialityOctadPairSign a b e * trialityIntegerMatrix e f := by
  rw [trialityOctadPairFlip_xor]
  simp only [trialityIntegerMatrix]
  rw [trialityHadamard_symmetric e, trialityHadamard_xor,
    trialityOctadPairShift_hadamard a b hab, trialityHadamard_symmetric f e]
  ring

/-- Row translation combines the character with the polarized quadratic sign. -/
theorem trialityIntegerMatrix_pair_flip_row (a b : Fin 8) (hab : a ≠ b)
    (e f : Fin 64) :
    trialityIntegerMatrix (trialityOctadPairFlip a b e) f =
      -trialityOctadPairSign a b e * trialityOctadPairSign a b f *
        trialityIntegerMatrix e f := by
  rw [trialityOctadPairFlip_xor]
  simp only [trialityIntegerMatrix]
  rw [trialityIntegerDiagonal_xor, trialityHadamard_xor,
    trialityOctadPairShift_diagonal a b hab,
    trialityHadamard_symmetric e, trialityOctadPairShift_hadamard a b hab,
    trialityOctadPairShift_hadamard a b hab]
  ring

-- The even-representative pairing has zero diagonal (64 individual bits).
theorem octadPairHadamard_diagonal_one : ∀ e : Fin 64, trialityHadamard e e = 1 := by
  decide +kernel

/-- The pair character is unchanged by its own normalized pair translation. -/
theorem trialityOctadPairSign_flip (a b : Fin 8) (hab : a ≠ b) (e : Fin 64) :
    trialityOctadPairSign a b (trialityOctadPairFlip a b e) = trialityOctadPairSign a b e := by
  rw [← trialityOctadPairShift_hadamard a b hab, trialityOctadPairFlip_xor,
    trialityHadamard_symmetric (trialityOctadPairShift a b), trialityHadamard_xor,
    octadPairHadamard_diagonal_one, mul_one,
    trialityHadamard_symmetric e, trialityOctadPairShift_hadamard a b hab]

/-- Local A acts on each sign label by the pair character. -/
def trialityOctadPairA (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℤ :=
  Matrix.diagonal (trialityOctadPairSign a b)

/-- Local B sends a label to its flipped label with negative pair character. -/
def trialityOctadPairB (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℤ :=
  fun e f => if e = trialityOctadPairFlip a b f then -trialityOctadPairSign a b f else 0

/-- Local C is the unsigned normalized pair flip. -/
def trialityOctadPairC (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℤ :=
  fun e f => if e = trialityOctadPairFlip a b f then 1 else 0

theorem trialityOctadPairFlip_eq_iff (a b : Fin 8) (e f : Fin 64) :
    e = trialityOctadPairFlip a b f ↔ f = trialityOctadPairFlip a b e := by
  constructor
  · intro h
    rw [h, trialityOctadPairFlip_involutive a b f]
  · intro h
    rw [h, trialityOctadPairFlip_involutive a b e]

/-- Left signed-shift multiplication selects the inverse-flipped row. -/
theorem trialityOctadPairB_mul (a b : Fin 8) (M : Matrix (Fin 64) (Fin 64) ℤ)
    (e f : Fin 64) :
    (trialityOctadPairB a b * M) e f =
      -trialityOctadPairSign a b (trialityOctadPairFlip a b e) *
        M (trialityOctadPairFlip a b e) f := by
  rw [Matrix.mul_apply]
  simp only [trialityOctadPairB, trialityOctadPairFlip_eq_iff, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Left unsigned-shift multiplication selects the inverse-flipped row. -/
theorem trialityOctadPairC_mul (a b : Fin 8) (M : Matrix (Fin 64) (Fin 64) ℤ)
    (e f : Fin 64) :
    (trialityOctadPairC a b * M) e f = M (trialityOctadPairFlip a b e) f := by
  rw [Matrix.mul_apply]
  simp only [trialityOctadPairC, trialityOctadPairFlip_eq_iff, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Right signed-shift multiplication selects the flipped column. -/
theorem mul_trialityOctadPairB (a b : Fin 8) (M : Matrix (Fin 64) (Fin 64) ℤ)
    (e f : Fin 64) :
    (M * trialityOctadPairB a b) e f =
      M e (trialityOctadPairFlip a b f) * -trialityOctadPairSign a b f := by
  rw [Matrix.mul_apply]
  simp only [trialityOctadPairB, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Right unsigned-shift multiplication selects the flipped column. -/
theorem mul_trialityOctadPairC (a b : Fin 8) (M : Matrix (Fin 64) (Fin 64) ℤ)
    (e f : Fin 64) :
    (M * trialityOctadPairC a b) e f = M e (trialityOctadPairFlip a b f) := by
  rw [Matrix.mul_apply]
  simp only [trialityOctadPairC, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Source Fourier triality conjugates local A to local B. -/
theorem trialityOctadPair_fourier_AB (a b : Fin 8) (hab : a ≠ b) :
    trialityIntegerMatrix * trialityOctadPairA a b =
      trialityOctadPairB a b * trialityIntegerMatrix := by
  ext e f
  rw [trialityOctadPairA, Matrix.mul_diagonal, trialityOctadPairB_mul,
    trialityOctadPairSign_flip a b hab, trialityIntegerMatrix_pair_flip_row a b hab]
  have hs := trialityOctadPairSign_sq a b e
  linear_combination -trialityOctadPairSign a b f * trialityIntegerMatrix e f * hs

/-- Source Fourier triality conjugates local B to local C. -/
theorem trialityOctadPair_fourier_BC (a b : Fin 8) (hab : a ≠ b) :
    trialityIntegerMatrix * trialityOctadPairB a b =
      trialityOctadPairC a b * trialityIntegerMatrix := by
  ext e f
  rw [mul_trialityOctadPairB, trialityOctadPairC_mul,
    trialityIntegerMatrix_pair_flip_column a b hab,
    trialityIntegerMatrix_pair_flip_row a b hab]
  ring

/-- Source Fourier triality conjugates local C to local A. -/
theorem trialityOctadPair_fourier_CA (a b : Fin 8) (hab : a ≠ b) :
    trialityIntegerMatrix * trialityOctadPairC a b =
      trialityOctadPairA a b * trialityIntegerMatrix := by
  ext e f
  rw [mul_trialityOctadPairC, trialityOctadPairA, Matrix.diagonal_mul,
    trialityIntegerMatrix_pair_flip_column a b hab]

/-- The local A/B/C action matrices in the actual real octad space. -/
def trialityOctadPairAReal (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℝ :=
  (trialityOctadPairA a b).map (Int.castRingHom ℝ)
def trialityOctadPairBReal (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℝ :=
  (trialityOctadPairB a b).map (Int.castRingHom ℝ)
def trialityOctadPairCReal (a b : Fin 8) : Matrix (Fin 64) (Fin 64) ℝ :=
  (trialityOctadPairC a b).map (Int.castRingHom ℝ)

theorem trialityOctadPairAReal_mulVec (a b : Fin 8) (x : Fin 64 → ℝ) (e : Fin 64) :
    (trialityOctadPairAReal a b).mulVec x e = (trialityOctadPairSign a b e : ℝ) * x e := by
  simp [trialityOctadPairAReal, trialityOctadPairA, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply]

theorem trialityOctadPairBReal_mulVec (a b : Fin 8) (hab : a ≠ b)
    (x : Fin 64 → ℝ) (e : Fin 64) :
    (trialityOctadPairBReal a b).mulVec x e =
      -(trialityOctadPairSign a b e : ℝ) * x (trialityOctadPairFlip a b e) := by
  simp [trialityOctadPairBReal, trialityOctadPairB, Matrix.mulVec, dotProduct,
    trialityOctadPairFlip_eq_iff a b e, trialityOctadPairSign_flip a b hab]

theorem trialityOctadPairCReal_mulVec (a b : Fin 8) (x : Fin 64 → ℝ) (e : Fin 64) :
    (trialityOctadPairCReal a b).mulVec x e = x (trialityOctadPairFlip a b e) := by
  simp [trialityOctadPairCReal, trialityOctadPairC, Matrix.mulVec, dotProduct,
    trialityOctadPairFlip_eq_iff a b e]

/-- Integer Fourier intertwining transports to the normalized actual real triality matrix. -/
theorem octadPair_real_intertwining (P Q : Matrix (Fin 64) (Fin 64) ℤ)
    (h : trialityIntegerMatrix * P = Q * trialityIntegerMatrix) :
    trialityRealMatrix * P.map (Int.castRingHom ℝ) =
      Q.map (Int.castRingHom ℝ) * trialityRealMatrix := by
  have hc : trialityIntegerMatrix.map (Int.castRingHom ℝ) * P.map (Int.castRingHom ℝ) =
      Q.map (Int.castRingHom ℝ) * trialityIntegerMatrix.map (Int.castRingHom ℝ) := by
    change (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix *
      (Int.castRingHom ℝ).mapMatrix P =
        (Int.castRingHom ℝ).mapMatrix Q * (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix
    rw [← map_mul, ← map_mul, h]
  simp only [trialityRealMatrix, Matrix.smul_mul, Matrix.mul_smul]
  rw [hc]

theorem trialityOctadPair_real_AB (a b : Fin 8) (hab : a ≠ b) :
    trialityRealMatrix * trialityOctadPairAReal a b =
      trialityOctadPairBReal a b * trialityRealMatrix :=
  octadPair_real_intertwining _ _ (trialityOctadPair_fourier_AB a b hab)

theorem trialityOctadPair_real_BC (a b : Fin 8) (hab : a ≠ b) :
    trialityRealMatrix * trialityOctadPairBReal a b =
      trialityOctadPairCReal a b * trialityRealMatrix :=
  octadPair_real_intertwining _ _ (trialityOctadPair_fourier_BC a b hab)

theorem trialityOctadPair_real_CA (a b : Fin 8) (hab : a ≠ b) :
    trialityRealMatrix * trialityOctadPairCReal a b =
      trialityOctadPairAReal a b * trialityRealMatrix :=
  octadPair_real_intertwining _ _ (trialityOctadPair_fourier_CA a b hab)

/-- The actual octad operation carries the local A action to B. -/
theorem trialityOctadPair_action_AB (a b : Fin 8) (hab : a ≠ b) (x : Fin 64 → ℝ) :
    trialityOctadAction ((trialityOctadPairAReal a b).mulVec x) =
      (trialityOctadPairBReal a b).mulVec (trialityOctadAction x) := by
  rw [trialityOctadAction_matrix, trialityOctadAction_matrix, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, trialityOctadPair_real_AB a b hab]

/-- The actual octad operation carries the local B action to C. -/
theorem trialityOctadPair_action_BC (a b : Fin 8) (hab : a ≠ b) (x : Fin 64 → ℝ) :
    trialityOctadAction ((trialityOctadPairBReal a b).mulVec x) =
      (trialityOctadPairCReal a b).mulVec (trialityOctadAction x) := by
  rw [trialityOctadAction_matrix, trialityOctadAction_matrix, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, trialityOctadPair_real_BC a b hab]

/-- The actual octad operation carries the local C action to A. -/
theorem trialityOctadPair_action_CA (a b : Fin 8) (hab : a ≠ b) (x : Fin 64 → ℝ) :
    trialityOctadAction ((trialityOctadPairCReal a b).mulVec x) =
      (trialityOctadPairAReal a b).mulVec (trialityOctadAction x) := by
  rw [trialityOctadAction_matrix, trialityOctadAction_matrix, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, trialityOctadPair_real_CA a b hab]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
