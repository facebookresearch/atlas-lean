/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Explicit triality in the dictionary coordinates of Martin Seysen,
*A computer-friendly construction of the monster*, arXiv:2002.10921v3,
§8.1, equations (8.1.1)–(8.1.4) and Table 5.

The A/B/C dictionary vectors all have squared norm 2; the 24 diagonal
vectors and the octad and X/Y/Z dictionary vectors have squared norm 1.
This module constructs a linear equivalence and proves its inverse laws.
It neither assumes nor proves that the FLM product is preserved.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators Kronecker

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster


/-- The two-dimensional Hadamard matrix used in the Sylvester construction. -/
def trialityHadamard2 : Matrix (Fin 2) (Fin 2) ℤ := fun i j => if i = 0 ∨ j = 0 then 1 else -1
/-- The initial matrix is Hadamard, with all four entries checked in Lean. -/
theorem triality_hadamard2_isHadamard : trialityHadamard2.IsHadamard := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [trialityHadamard2, Unitary.mem_iff]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [trialityHadamard2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [trialityHadamard2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Flatten the two-by-power-of-two Kronecker index. -/
def trialitySylvesterIndex (n : ℕ) : Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by omega))

/-- Iterated Sylvester Hadamard matrix, used to certify the octad transform. -/
def trialitySylvester : (n : ℕ) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ
  | 0 => 1
  | n + 1 =>
    Matrix.reindex (trialitySylvesterIndex n) (trialitySylvesterIndex n)
      (trialityHadamard2 ⊗ₖ trialitySylvester n)

/-- Orthogonality follows inductively from the Kronecker-product theorem. -/
theorem triality_sylvester_isHadamard (n : ℕ) : (trialitySylvester n).IsHadamard := by
  induction n with
  | zero =>
    constructor
    · intro i j
      have hi : i = 0 := by
        apply Fin.ext
        have h := i.isLt
        norm_num at h
        omega
      have hj : j = 0 := by
        apply Fin.ext
        have h := j.isLt
        norm_num at h
        omega
      subst i j
      norm_num [trialitySylvester, Matrix.one_apply, Unitary.mem_iff]
    · simp [trialitySylvester]
    · simp [trialitySylvester]
  | succ n hn =>
    exact (triality_hadamard2_isHadamard.kronecker hn).reindex
      (trialitySylvesterIndex n) (trialitySylvesterIndex n)

/-- Count the occupied positions among the first eight bits of a mask. -/
def trialityBitWeight8 (x : ℕ) : ℕ := ∑ i : Fin 8, if x.testBit i.val then 1 else 0
/-- Represent even subsets of an octad modulo complementation: the last bit is
zero, the first six bits are free, and bit six enforces even cardinality.
Source: Seysen §8.1, equation (8.1.4). -/
def trialityEvenMask (x : Fin 64) : ℕ := x.val + 64 * (trialityBitWeight8 x.val % 2)
/-- Octad Fourier matrix with entry `(-1)^|delta intersection epsilon|`,
using the explicit representatives from `trialityEvenMask`. -/
def trialityHadamard : Matrix (Fin 64) (Fin 64) ℤ :=
  fun i j =>
    if (trialityBitWeight8 (trialityEvenMask i &&& trialityEvenMask j) % 2) = 0 then 1 else -1

/-- The bit permutation converting the even-subset pairing to the Walsh pairing. -/
def trialityTwist (i : Fin 64) : Fin 64 :=
  ⟨(i.val ^^^ if trialityBitWeight8 i.val % 2 = 0 then 0 else 63) % 64, by omega⟩
set_option maxHeartbeats 0 in
-- Kernel reduction of the finite coordinate equality exceeds the default elaboration limit.
set_option maxRecDepth 10000 in
/-- The conversion is an involution, checked on its 64 arguments in the kernel. -/
theorem triality_twist_involutive : Function.Involutive trialityTwist := by
  change ∀ i, trialityTwist (trialityTwist i) = i
  decide +kernel

/-- The certified bit permutation. -/
def trialityTwistEquiv : Equiv.Perm (Fin 64) where
  toFun := trialityTwist
  invFun := trialityTwist
  left_inv := triality_twist_involutive
  right_inv := triality_twist_involutive

set_option maxHeartbeats 0 in
-- Kernel reduction of the finite coordinate equality exceeds the default elaboration limit.
set_option maxRecDepth 10000 in
/-- The source matrix is a row permutation of the sixfold Sylvester matrix.
This finite equality is kernel-checked; no `native_decide` is used. -/
theorem triality_hadamard_eq_sylvester :
    trialityHadamard = (trialitySylvester 6).submatrix trialityTwistEquiv (Equiv.refl _) := by
  decide +kernel

/-- The source matrix is Hadamard. -/
theorem triality_hadamard_isHadamard : trialityHadamard.IsHadamard := by
  rw [triality_hadamard_eq_sylvester]
  exact (Matrix.isHadamard_submatrix_equiv_iff trialityTwistEquiv (Equiv.refl _)).mpr
    (triality_sylvester_isHadamard 6)

/-- The unnormalized octad Fourier matrix has square 64 times the identity. -/
theorem triality_hadamard_square :
    trialityHadamard * trialityHadamard = 64 • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
  have ht : trialityHadamard.conjTranspose = trialityHadamard := by
    ext i j
    simp [Matrix.conjTranspose_apply, trialityHadamard, Nat.and_comm]
  have hh := triality_hadamard_isHadamard.mul_conjTranspose
  rw [ht] at hh
  simpa [Nat.cast_smul_eq_nsmul] using hh

/-- The Fourier matrix scaled by 1/8, as in Seysen equation (8.1.4). -/
noncomputable def trialityNormalizedHadamard : Matrix (Fin 64) (Fin 64) ℝ :=
  (1 / 8 : ℝ) • trialityHadamard.map (Int.castRingHom ℝ)

/-- The normalized Fourier transform is its own inverse over the reals. -/
theorem triality_normalized_hadamard_square :
    trialityNormalizedHadamard * trialityNormalizedHadamard = 1 := by
  have hm : trialityHadamard.map (Int.castRingHom ℝ) * trialityHadamard.map (Int.castRingHom ℝ) =
      (64 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) := by
    change (Int.castRingHom ℝ).mapMatrix trialityHadamard *
      (Int.castRingHom ℝ).mapMatrix trialityHadamard = _
    rw [← map_mul, triality_hadamard_square]
    ext i j
    by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.ofNat_apply, h]
  unfold trialityNormalizedHadamard
  rw [Matrix.smul_mul, Matrix.mul_smul, hm, smul_smul, smul_smul]
  norm_num

/-- The Fourier transform with its inverse laws proved. -/
noncomputable def trialityHadamardEquiv : (Fin 64 → ℝ) ≃ₗ[ℝ] (Fin 64 → ℝ) :=
  Matrix.toLin'OfInv triality_normalized_hadamard_square triality_normalized_hadamard_square

/-- Diagonal signs `(-1)^(|delta|/2)` from Seysen equation (8.1.4),
with inverse given by the same signs. -/
noncomputable def trialitySignEquiv : (Fin 64 → ℝ) ≃ₗ[ℝ] (Fin 64 → ℝ) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ
    (if trialityBitWeight8 (trialityEvenMask i) / 2 % 2 = 0 then (1 : ℝ) else -1)
    (by split <;> norm_num)

/-- Split a coordinate space at a specified block boundary. -/
def trialityBlockSplit (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) × (Fin m → ℝ)) :=
  { (Fin.appendEquiv n m).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Regard a flat block as rectangular coordinates, in row-major order. -/
def trialityBlockUncurry (n m : ℕ) : (Fin (n * m) → ℝ) ≃ₗ[ℝ] (Fin n → Fin m → ℝ) where
  toFun f i j := f (finProdFinEquiv (i, j))
  invFun f k := f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv f := by
    ext k
    exact congrArg f (Equiv.apply_symm_apply finProdFinEquiv k)
  right_inv f := by ext i j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Dictionary coordinates from Seysen §8.1, Table 5: 24 diagonals,
three 276-dimensional blocks, 759 octad blocks of size 64, and
three blocks of size 2048 times 24. -/
abbrev TrialityBlocks := (Fin 24 → ℝ) × ((Fin 3 → Fin 276 → ℝ) ×
  ((Fin 759 → Fin 64 → ℝ) × (Fin 3 → Fin 49152 → ℝ)))

/-- Explicit block indexing of the fixed 196884-dimensional coordinate space. -/
def trialityBlocksEquiv : (Fin 196884 → ℝ) ≃ₗ[ℝ] TrialityBlocks :=
  (trialityBlockSplit 24 196860).trans
    ((LinearEquiv.refl ℝ _).prodCongr
      ((trialityBlockSplit 828 196032).trans
        ((trialityBlockUncurry 3 276).prodCongr
          ((trialityBlockSplit 48576 147456).trans
            ((trialityBlockUncurry 759 64).prodCongr (trialityBlockUncurry 3 49152))))))

/-- The permutation 0 to 1 to 2 to 0. -/
def trialityCycle : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)

/-- Cycle the three dictionary blocks by moving their basis vectors forward. -/
def trialityCycleAction (n : ℕ) : (Fin 3 → Fin n → ℝ) ≃ₗ[ℝ] (Fin 3 → Fin n → ℝ) :=
  LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 3 => Fin n → ℝ) trialityCycle

/-- The triality operation on an octad block: Fourier transform followed
by the diagonal signs, corresponding to `tau = y_tau x_tau` in the
right-action convention of Seysen §8.1. -/
noncomputable def trialityOctadAction : (Fin 64 → ℝ) ≃ₗ[ℝ] (Fin 64 → ℝ) :=
  trialityHadamardEquiv.trans trialitySignEquiv

/-- Fix the diagonal block, cycle the two triples of dictionary blocks,
and apply the same octad operation on each of the 759 octads. -/
noncomputable def trialityBlockAction : TrialityBlocks ≃ₗ[ℝ] TrialityBlocks :=
  (LinearEquiv.refl ℝ _).prodCongr ((trialityCycleAction 276).prodCongr
    ((LinearEquiv.piCongrRight fun _ : Fin 759 => trialityOctadAction).prodCongr
      (trialityCycleAction 49152)))

/-- The explicit triality equivalence in the dictionary basis of Seysen §8.1.
All linearity and inverse laws are proved. Compatibility with the FLM
construction and preservation of its product are separate obligations. -/
noncomputable def griessTriality : (Fin 196884 → ℝ) ≃ₗ[ℝ] (Fin 196884 → ℝ) :=
  trialityBlocksEquiv.trans (trialityBlockAction.trans trialityBlocksEquiv.symm)


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
