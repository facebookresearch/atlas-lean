/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.Symmetry
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.Symmetry`

* Restriction: `C6lat` has trace `1` and order `6`; `C4` has trace `0` and
  order `4`; the order-5 rotation with `cos = (√5-1)/4` has non-integer trace,
  so it is neither a lattice endomorphism nor a lattice symmetry.
* Lattice maps: doubling on `ℤ` is a lattice endomorphism but not a lattice
  symmetry; the integer matrices `C4`, `C6lat` and `Rz90` of finite order are
  lattice symmetries.
* Point groups: orthogonality (except for the lattice-basis matrix `C6lat`),
  orders, determinants, and traces for every concrete matrix in the module.
* Neumann: a rank-3 tensor with `T 0 0 0 = 1` is not inversion-invariant; the
  diagonal matrix `diag(1,2,3)` and a matrix with nonzero off-diagonal are not
  cubic-invariant.
* Elastic: `upperTri.card = 21` by independent computation; cubic/isotropic
  instances; a cubic matrix violating `(c11-c12) = 2*c44` is not invariant
  under the `45°` rotation `Rz45`; axis permutations alone do not imply the
  cubic form (counterexample).
* Rotation action: the identity acts trivially, the quarter-turn entry
  equation is invariance under `Rz90ᵀ` (not `Rz90`), the cubic family is fixed by
  the quarter-turn `Rz90`, the Lamé family is fixed by `Rz45` and `Rx90`, and
  the hypotheses of `eq_isotropicVoigt_of_rotationInvariance` are satisfiable.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.Symmetry

open _root_.Crystallography.Symmetry
open scoped Matrix

/-! ### Restriction checks -/

example : C6lat.trace = 1 := C6lat_trace

example : C6lat ^ 6 = 1 ∧ ∀ m : ℕ, 0 < m → m < 6 → C6lat ^ m ≠ 1 :=
  C6lat_order

example : C4.trace = 0 := C4_trace

example : C4 ^ 4 = 1 ∧ ∀ m : ℕ, 0 < m → m < 4 → C4 ^ m ≠ 1 := C4_order

/-- A general `2 × 2` rotation matrix. -/
def rotMat (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, -s; s, c]

/-- Fifth power of an order-five rotation is `1`. -/
lemma rotMat_pow5 (c s : ℝ) (hc : 4 * c ^ 2 + 2 * c - 1 = 0)
    (hs : c ^ 2 + s ^ 2 = 1) : (rotMat c s) ^ 5 = 1 := by
  have e5 : (rotMat c s) ^ 5 = (rotMat c s) ^ 2 * (rotMat c s) ^ 3 :=
    pow_add (rotMat c s) 2 3
  have e3 : (rotMat c s) ^ 3 = (rotMat c s) ^ 2 * rotMat c s :=
    pow_succ (rotMat c s) 2
  have e2 : (rotMat c s) ^ 2 = rotMat c s * rotMat c s :=
    pow_two (rotMat c s)
  refine Matrix.ext ?_
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e5, e3, e2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat, Matrix.of_apply]
    linear_combination (4 * c ^ 3 - 2 * c ^ 2 - 3 * c + 1) * hc +
      (-15 * c ^ 3 + 5 * c + 5 * c * s ^ 2) * hs
  · rw [e5, e3, e2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat, Matrix.of_apply]
    linear_combination (-(s * (4 * c ^ 2 - 2 * c - 1))) * hc +
      (-(s - 11 * c ^ 2 * s + s ^ 3)) * hs
  · rw [e5, e3, e2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat, Matrix.of_apply]
    linear_combination (s * (4 * c ^ 2 - 2 * c - 1)) * hc +
      (s - 11 * c ^ 2 * s + s ^ 3) * hs
  · rw [e5, e3, e2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat, Matrix.of_apply]
    linear_combination (4 * c ^ 3 - 2 * c ^ 2 - 3 * c + 1) * hc +
      (-15 * c ^ 3 + 5 * c + 5 * c * s ^ 2) * hs

/-- An order-five rotation is not the identity at powers 1–4. -/
lemma rotMat_ne_one (c s : ℝ) (hc : 4 * c ^ 2 + 2 * c - 1 = 0)
    (hs : c ^ 2 + s ^ 2 = 1) (m : ℕ) (hmpos : 0 < m) (hmlt : m < 5) :
    (rotMat c s) ^ m ≠ 1 := by
  have e2 : (rotMat c s) ^ 2 = rotMat c s * rotMat c s :=
    pow_two (rotMat c s)
  have e3 : (rotMat c s) ^ 3 = (rotMat c s) ^ 2 * rotMat c s :=
    pow_succ (rotMat c s) 2
  have e4 : (rotMat c s) ^ 4 = (rotMat c s) ^ 2 * (rotMat c s) ^ 2 :=
    pow_add (rotMat c s) 2 2
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    simp [pow_one, rotMat, Matrix.of_apply] at e
    rw [e] at hc
    norm_num at hc
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    rw [e2] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat,
      Matrix.of_apply] at e
    have f5 : (5 : ℝ) = 0 := by
      linear_combination (4 * c - 4) * e + (4 * c - 4) * hs + (3 - 2 * c) * hc
    norm_num at f5
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    rw [e3, e2] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat,
      Matrix.of_apply] at e
    have f5 : (5 : ℝ) = 0 := by
      linear_combination (4 * c - 4) * e + (12 * c ^ 2 - 12 * c) * hs +
        (-4 * c ^ 2 + 6 * c - 1) * hc
    norm_num at f5
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    rw [e4, e2] at e
    simp [Matrix.mul_apply, Fin.sum_univ_two, rotMat,
      Matrix.of_apply] at e
    have f5 : (5 : ℝ) = 0 := by
      linear_combination (-(4 * c + 6)) * e +
        (4 * c * s ^ 2 + 6 * s ^ 2 - 28 * c ^ 3 - 42 * c ^ 2 + 4 * c + 6) * hs +
        (8 * c ^ 3 + 8 * c ^ 2 - 10 * c - 5) * hc
    norm_num at f5

/-- `cos 72° = (√5-1)/4`. -/
noncomputable def c72 : ℝ := (Real.sqrt 5 - 1) / 4

/-- `sin 72°`, via `sin² + cos² = 1`. -/
noncomputable def s72 : ℝ := Real.sqrt (1 - c72 ^ 2)

/-- The Cartesian 72° rotation matrix. -/
noncomputable def R72 : Matrix (Fin 2) (Fin 2) ℝ := rotMat c72 s72

/-- `c72` satisfies `4c² + 2c - 1 = 0`. -/
lemma R72_hc : 4 * c72 ^ 2 + 2 * c72 - 1 = 0 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  show 4 * (((Real.sqrt 5 - 1) / 4)) ^ 2 + 2 * (((Real.sqrt 5 - 1) / 4)) - 1
    = 0
  linear_combination (1 / 4 : ℝ) * hsqrt

/-- `c72² + s72² = 1`. -/
lemma R72_hs : c72 ^ 2 + s72 ^ 2 = 1 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlt : c72 ^ 2 < 1 := by
    show ((Real.sqrt 5 - 1) / 4) ^ 2 < 1
    nlinarith [hsqrt, Real.sqrt_nonneg 5]
  have hnn : 0 ≤ 1 - c72 ^ 2 := by linarith
  have hsq : s72 ^ 2 = 1 - c72 ^ 2 := Real.sq_sqrt hnn
  linarith

/-- `R72` has order five: `R72^5 = 1`. -/
lemma R72_order5 : R72 ^ 5 = 1 := rotMat_pow5 c72 s72 R72_hc R72_hs

/-- `R72` is not the identity at powers 1–4. -/
lemma R72_minimal (m : ℕ) (hmpos : 0 < m) (hmlt : m < 5) :
    R72 ^ m ≠ 1 :=
  rotMat_ne_one c72 s72 R72_hc R72_hs m hmpos hmlt

/-- `R72` has trace `(√5-1)/2`. -/
lemma R72_trace : R72.trace = (Real.sqrt 5 - 1) / 2 := by
  have e : R72.trace = c72 + c72 := by
    simp [R72, rotMat, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
      Matrix.of_apply]
  rw [e, show c72 = (Real.sqrt 5 - 1) / 4 from rfl]
  ring

/-- The trace of `R72` is not an integer. -/
lemma R72_trace_not_integer : ¬ ∃ k : ℤ, R72.trace = k := by
  rintro ⟨k, hk⟩
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have ht : R72.trace ^ 2 + R72.trace - 1 = 0 := by
    rw [R72_trace]
    linear_combination (1 / 4 : ℝ) * hsqrt
  rw [hk] at ht
  have hkz : k ^ 2 + k - 1 = 0 := by
    have ht2 : ((k ^ 2 + k - 1 : ℤ) : ℝ) = 0 := by
      push_cast
      linarith [ht]
    exact_mod_cast ht2
  have hmul : k * (k + 1) = 1 := by linear_combination hkz
  have hkunit : k = 1 ∨ k = -1 :=
    Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨k + 1, hmul.symm⟩)
  rcases hkunit with rfl | rfl <;> norm_num at hkz

/-- `R72` is not a lattice endomorphism. -/
lemma R72_not_latticeEndomorphism : ¬ IsLatticeEndomorphism 2 R72 := by
  intro hlat
  exact R72_trace_not_integer (trace_integer_two R72 hlat)

/-- `R72` is not a lattice symmetry: it maps no full-rank lattice onto itself. -/
lemma R72_not_latticeSymmetry : ¬ IsLatticeSymmetry 2 R72 := fun h =>
  R72_not_latticeEndomorphism h.isLatticeEndomorphism

/-! ### Lattice endomorphisms and lattice symmetries -/

/-- Doubling on `ℤ` is a lattice endomorphism. -/
lemma doubling_latticeEndomorphism : IsLatticeEndomorphism 1 !![(2 : ℝ)] :=
  ⟨!![2], 1, by simp, by ext i j; fin_cases i; fin_cases j; simp⟩

/-- Doubling is not a lattice symmetry: it maps every full-rank lattice of the
line onto a proper sublattice, so `IsLatticeEndomorphism` alone does not give a
symmetry. -/
lemma doubling_not_latticeSymmetry : ¬ IsLatticeSymmetry 1 !![(2 : ℝ)] := by
  rintro ⟨P, hP, hL⟩
  have hP0 : P 0 0 ≠ 0 := by
    have h := hP.ne_zero
    rwa [Matrix.det_unique] at h
  have hv : (P *ᵥ fun _ => ((1 : ℤ) : ℝ)) ∈ basisLattice 1 P := ⟨fun _ => 1, rfl⟩
  rw [← hL] at hv
  obtain ⟨_, ⟨z, rfl⟩, hw⟩ := hv
  have e := congrFun hw 0
  simp [Matrix.mulVec, dotProduct] at e
  have hz : (2 * z 0 : ℝ) = 1 := by
    have e' : P 0 0 * (2 * z 0 - 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp e' with h | h
    · exact absurd h hP0
    · linarith
  have hz' : 2 * z 0 = 1 := by exact_mod_cast hz
  omega

/-- `C4` maps `ℤ²` onto itself: an integer matrix of finite order is a lattice
symmetry. -/
lemma C4_latticeSymmetry : IsLatticeSymmetry 2 C4 :=
  IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one
    ⟨!![0, -1; 1, 0], 1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [C4]⟩
    (by norm_num) C4_order.1

/-- `C6lat` maps `ℤ²` onto itself. -/
lemma C6lat_latticeSymmetry : IsLatticeSymmetry 2 C6lat :=
  IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one
    ⟨!![1, -1; 1, 0], 1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [C6lat]⟩
    (by norm_num) C6lat_order.1

/-- `Rz90` maps `ℤ³` onto itself. -/
lemma Rz90_latticeSymmetry : IsLatticeSymmetry 3 Rz90 :=
  IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one
    ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], 1, by simp,
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Rz90]⟩
    (by norm_num) Rz90_order.1

/-! ### Point-group checks -/

example : C2ᵀ * C2 = 1 ∧ C2.det = 1 ∧ C2 ^ 2 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 2 → C2 ^ m ≠ 1) ∧ C2.trace = -2 :=
  ⟨C2_orthogonal, C2_det, C2_order.1, C2_order.2, C2_trace⟩

example : C4ᵀ * C4 = 1 ∧ C4.det = 1 ∧ C4 ^ 4 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 4 → C4 ^ m ≠ 1) ∧ C4.trace = 0 :=
  ⟨C4_orthogonal, C4_det, C4_order.1, C4_order.2, C4_trace⟩

example : C6lat.det = 1 ∧ C6lat ^ 6 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 6 → C6lat ^ m ≠ 1) ∧ C6lat.trace = 1 :=
  ⟨C6lat_det, C6lat_order.1, C6lat_order.2, C6lat_trace⟩

example : mirrorᵀ * mirror = 1 ∧ mirror.det = -1 ∧ mirror ^ 2 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 2 → mirror ^ m ≠ 1) ∧ mirror.trace = 0 :=
  ⟨mirror_orthogonal, mirror_det, mirror_order.1, mirror_order.2,
    mirror_trace⟩

example : Rx90ᵀ * Rx90 = 1 ∧ Rx90.det = 1 ∧ Rx90 ^ 4 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 4 → Rx90 ^ m ≠ 1) ∧ Rx90.trace = 1 :=
  ⟨Rx90_orthogonal, Rx90_det, Rx90_order.1, Rx90_order.2, Rx90_trace⟩

example : Ry90ᵀ * Ry90 = 1 ∧ Ry90.det = 1 ∧ Ry90 ^ 4 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 4 → Ry90 ^ m ≠ 1) ∧ Ry90.trace = 1 :=
  ⟨Ry90_orthogonal, Ry90_det, Ry90_order.1, Ry90_order.2, Ry90_trace⟩

example : Rz90ᵀ * Rz90 = 1 ∧ Rz90.det = 1 ∧ Rz90 ^ 4 = 1 ∧
    (∀ m : ℕ, 0 < m → m < 4 → Rz90 ^ m ≠ 1) ∧ Rz90.trace = 1 :=
  ⟨Rz90_orthogonal, Rz90_det, Rz90_order.1, Rz90_order.2, Rz90_trace⟩

example : IsSignedPerm Rx90 ∧ IsSignedPerm Ry90 ∧ IsSignedPerm Rz90 :=
  ⟨Rx90_signed, Ry90_signed, Rz90_signed⟩

/-! ### Neumann checks -/

/-- A rank-3 tensor with `T 0 0 0 = 1` cannot be inversion-invariant. -/
lemma rank3_nonzero_not_inversionInvariant (T : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hT : T 0 0 0 = 1) : ¬ ∀ i j k, T i j k = -T i j k := by
  intro h
  have h0 := polarRank3_inversion T h
  have e := congrArg (fun F : Fin 3 → Fin 3 → Fin 3 → ℝ => F 0 0 0) h0
  rw [hT] at e
  simp only [Pi.zero_apply] at e
  norm_num at e

/-- `diag(1,2,3)` for the cubic countermodel. -/
def diag123 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 2, 0; 0, 0, 3]

/-- `diag(1,2,3)` is symmetric. -/
lemma diag123_symmetric : diag123ᵀ = diag123 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag123, Matrix.transpose_apply, Matrix.of_apply]

/-- `diag(1,2,3)` is not cubic-invariant (diagonals differ). -/
lemma diag123_not_cubicInvariant :
    ¬ (Rx90ᵀ * diag123 * Rx90 = diag123 ∧
      Ry90ᵀ * diag123 * Ry90 = diag123 ∧
      Rz90ᵀ * diag123 * Rz90 = diag123) := by
  rintro ⟨hx, hy, hz⟩
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hz
  norm_num [diag123, Rz90, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.transpose_apply, Matrix.of_apply] at e

/-! ### Elastic checks -/

/-- `upperTri.card = 21`, recomputed independently. -/
lemma test_upperTri_card : upperTri.card = 21 := by
  decide

/-- The cubic family instance `cubicVoigt 10 4 3` has the stated entries. -/
lemma test_cubicVoigt_entries :
    cubicVoigt 10 4 3 0 0 = 10 ∧ cubicVoigt 10 4 3 0 1 = 4 ∧
    cubicVoigt 10 4 3 3 3 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cubicVoigt, Matrix.of_apply]

/-- `isotropicVoigt 4 3 = cubicVoigt 10 4 3` since `4 + 2*3 = 10`. -/
lemma test_isotropicVoigt_instance :
    isotropicVoigt 4 3 = cubicVoigt 10 4 3 := by
  have h43 : (4 : ℝ) + 2 * 3 = 10 := by norm_num
  rw [isotropicVoigt_isCubic, h43]

/-- `cubicVoigt 10 4 2` violates the isotropy relation `(c11-c12) = 2*c44`. -/
lemma test_cubic_not_isotropic :
    (cubicVoigt 10 4 2) 0 0 - (cubicVoigt 10 4 2) 0 1 ≠
      2 * (cubicVoigt 10 4 2) 3 3 := by
  norm_num [cubicVoigt, Matrix.of_apply]

/-- A symmetric matrix with nonzero off-diagonal, for the countermodel. -/
def offDiagExample : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 1, 1, 0; 0, 0, 1]

/-- The countermodel is symmetric. -/
lemma offDiagExample_symmetric : offDiagExampleᵀ = offDiagExample := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagExample, Matrix.transpose_apply, Matrix.of_apply]

/-- The countermodel is not cubic-invariant. -/
lemma offDiagExample_not_cubicInvariant :
    ¬ (Rx90ᵀ * offDiagExample * Rx90 = offDiagExample ∧
      Ry90ᵀ * offDiagExample * Ry90 = offDiagExample ∧
      Rz90ᵀ * offDiagExample * Rz90 = offDiagExample) := by
  rintro ⟨hx, hy, hz⟩
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) hz
  norm_num [offDiagExample, Rz90, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.transpose_apply, Matrix.of_apply] at e

/-- Symmetry forbids `C 0 1 ≠ C 1 0`: the entries agree. -/
lemma symm_entries_agree (C : Matrix (Fin 6) (Fin 6) ℝ)
    (hC : Cᵀ = C) : C 0 1 = C 1 0 := by
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 1 0) hC
  simpa [Matrix.transpose_apply] using h

/-- A symmetric Voigt matrix invariant under all three axis swaps but not
cubic: `C03 = C14 = C25 = 1`. Axis permutations alone do not imply the cubic
form. -/
def voigtCounter : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0]

/-- The counterexample is symmetric. -/
lemma voigtCounter_symmetric : voigtCounterᵀ = voigtCounter := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [voigtCounter, Matrix.transpose_apply, Matrix.of_apply]

/-- The counterexample is invariant under the `x ↔ y` swap. -/
lemma voigtCounter_swap01 (i j : Fin 6) :
    voigtCounter i j = voigtCounter (voigtSwap01 i) (voigtSwap01 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [voigtCounter, Matrix.of_apply, voigtSwap01]

/-- The counterexample is invariant under the `x ↔ z` swap. -/
lemma voigtCounter_swap02 (i j : Fin 6) :
    voigtCounter i j = voigtCounter (voigtSwap02 i) (voigtSwap02 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [voigtCounter, Matrix.of_apply, voigtSwap02]

/-- The counterexample is invariant under the `y ↔ z` swap. -/
lemma voigtCounter_swap12 (i j : Fin 6) :
    voigtCounter i j = voigtCounter (voigtSwap12 i) (voigtSwap12 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [voigtCounter, Matrix.of_apply, voigtSwap12]

/-- The counterexample is not a cubic-family matrix. -/
lemma voigtCounter_not_cubic :
    voigtCounter ≠ cubicVoigt (voigtCounter 0 0) (voigtCounter 0 1)
      (voigtCounter 3 3) := by
  intro h
  have e := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 0 3) h
  norm_num [voigtCounter, cubicVoigt, Matrix.of_apply] at e

/-- Distinct constants give distinct cubic matrices. -/
lemma test_cubicVoigt_ne : cubicVoigt 10 4 2 ≠ cubicVoigt 10 4 3 := by
  intro h
  have e := (cubicVoigt_inj h).2.2
  norm_num at e

/-! ### Rotation-action checks -/

/-- The identity acts trivially on `cubicVoigt 10 4 2`. -/
lemma test_voigtRotate_one : voigtRotate 1 (cubicVoigt 10 4 2) = cubicVoigt 10 4 2 :=
  voigtRotate_one _

/-- `Rz45` is a proper rotation whose square is the quarter-turn `Rz90`. -/
lemma test_Rz45 : Rz45ᵀ * Rz45 = 1 ∧ Rz45.det = 1 ∧ Rz45 ^ 2 = Rz90 :=
  ⟨Rz45_orthogonal, Rz45_det, Rz45_sq⟩

/-- The `45°` rotation sends the shear entry of `cubicVoigt 10 4 2` to `3`. -/
lemma test_Rz45_shear : voigtRotate Rz45 (cubicVoigt 10 4 2) 5 5 = 3 := by
  rw [voigtRotate_Rz45_cubicVoigt_55]
  norm_num

/-- A cubic matrix violating `(c11-c12) = 2*c44` is not invariant under the
`45°` rotation about `z`. -/
lemma test_cubic_not_Rz45_invariant :
    voigtRotate Rz45 (cubicVoigt 10 4 2) ≠ cubicVoigt 10 4 2 := by
  intro h
  have e := relation_of_voigtRotate_Rz45 _ _ _ h
  norm_num at e

/-- The Lamé instance `isotropicVoigt 4 3` is fixed by `Rz45` and by `Rx90`. -/
lemma test_isotropic_invariant :
    voigtRotate Rz45 (isotropicVoigt 4 3) = isotropicVoigt 4 3 ∧
      voigtRotate Rx90 (isotropicVoigt 4 3) = isotropicVoigt 4 3 :=
  ⟨voigtRotate_isotropicVoigt _ Rz45_orthogonal _ _,
    voigtRotate_isotropicVoigt _ Rx90_orthogonal _ _⟩

/-- The quarter-turn entry equation is invariance under `Rz90ᵀ`: at `(0, 3)` it
reads `C 0 3 = -C 1 4`, while the inverse turn `Rz90` sends `C 0 3` to `C 1 4`. -/
lemma test_voigtRotZ90_inverse (C : Matrix (Fin 6) (Fin 6) ℝ) :
    voigtRotate Rz90ᵀ C 0 3 = -C 1 4 ∧ voigtRotate Rz90 C 0 3 = C 1 4 := by
  refine ⟨?_, ?_⟩
  · rw [voigtRotate_Rz90_transpose_apply]
    simp [voigtRotZ90, voigtRotZ90Sign]
  · simp [voigtRotate, Rz90, voigtFst, voigtSnd, voigtIndex, Fin.sum_univ_three]

/-- The `hrot` hypothesis of `eq_cubicVoigt_of_voigtInvariance` follows from
`voigtRotate Rz90ᵀ C = C`. -/
lemma test_hrot_of_voigtRotate (C : Matrix (Fin 6) (Fin 6) ℝ)
    (h : voigtRotate Rz90ᵀ C = C) (i j : Fin 6) :
    C i j = voigtRotZ90Sign i * voigtRotZ90Sign j * C (voigtRotZ90 i) (voigtRotZ90 j) := by
  rw [← voigtRotate_Rz90_transpose_apply, h]

set_option maxHeartbeats 1000000 in -- 36 entries, each a sum of 81 terms
/-- The tensor action agrees with the cubic invariance: every cubic matrix is
fixed by the quarter-turn `Rz90`, computed entry by entry. -/
lemma test_cubic_Rz90_invariant (c11 c12 c44 : ℝ) :
    voigtRotate Rz90 (cubicVoigt c11 c12 c44) = cubicVoigt c11 c12 c44 := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [voigtRotate, Rz90, cubicVoigt, voigtFst, voigtSnd, voigtIndex, Fin.sum_univ_three]

/-- The hypotheses of `eq_isotropicVoigt_of_rotationInvariance` hold for the
Lamé instance `isotropicVoigt 4 3`. -/
lemma test_isotropic_from_invariance :
    isotropicVoigt 4 3 =
      isotropicVoigt (isotropicVoigt 4 3 0 1) (isotropicVoigt 4 3 3 3) :=
  eq_isotropicVoigt_of_rotationInvariance _
    (by rw [isotropicVoigt_isCubic]; exact cubicVoigt_transpose _ _ _)
    (isotropicVoigt_swap01 4 3) (isotropicVoigt_swap02 4 3) (isotropicVoigt_swap12 4 3)
    (isotropicVoigt_rotZ90 4 3) (voigtRotate_isotropicVoigt _ Rz45_orthogonal _ _)

end PhyslibExtTest.CondensedMatter.Crystallography.Symmetry

#print axioms Crystallography.Symmetry.IsLatticeEndomorphism
#print axioms Crystallography.Symmetry.trace_integer_of_latticeEndomorphism
#print axioms Crystallography.Symmetry.trace_integer_two
#print axioms Crystallography.Symmetry.trace_integer_three
#print axioms Crystallography.Symmetry.basisLattice
#print axioms Crystallography.Symmetry.isLatticeEndomorphism_iff_mapsTo
#print axioms Crystallography.Symmetry.IsLatticeSymmetry
#print axioms Crystallography.Symmetry.IsLatticeSymmetry.isLatticeEndomorphism
#print axioms Crystallography.Symmetry.IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one
#print axioms Crystallography.Symmetry.exists_angle_of_trace_two
#print axioms Crystallography.Symmetry.crystallographic_restriction_two
#print axioms Crystallography.Symmetry.exists_angle_of_trace_three
#print axioms Crystallography.Symmetry.crystallographic_restriction_three
#print axioms Crystallography.Symmetry.C2
#print axioms Crystallography.Symmetry.C4
#print axioms Crystallography.Symmetry.C6lat
#print axioms Crystallography.Symmetry.mirror
#print axioms Crystallography.Symmetry.C2_orthogonal
#print axioms Crystallography.Symmetry.C2_det
#print axioms Crystallography.Symmetry.C2_order
#print axioms Crystallography.Symmetry.C2_trace
#print axioms Crystallography.Symmetry.C4_orthogonal
#print axioms Crystallography.Symmetry.C4_det
#print axioms Crystallography.Symmetry.C4_order
#print axioms Crystallography.Symmetry.C4_trace
#print axioms Crystallography.Symmetry.C6lat_det
#print axioms Crystallography.Symmetry.C6lat_order
#print axioms Crystallography.Symmetry.C6lat_trace
#print axioms Crystallography.Symmetry.mirror_orthogonal
#print axioms Crystallography.Symmetry.mirror_det
#print axioms Crystallography.Symmetry.mirror_order
#print axioms Crystallography.Symmetry.mirror_trace
#print axioms Crystallography.Symmetry.Rx90
#print axioms Crystallography.Symmetry.Ry90
#print axioms Crystallography.Symmetry.Rz90
#print axioms Crystallography.Symmetry.Rx90_orthogonal
#print axioms Crystallography.Symmetry.Rx90_det
#print axioms Crystallography.Symmetry.Rx90_order
#print axioms Crystallography.Symmetry.Rx90_trace
#print axioms Crystallography.Symmetry.Ry90_orthogonal
#print axioms Crystallography.Symmetry.Ry90_det
#print axioms Crystallography.Symmetry.Ry90_order
#print axioms Crystallography.Symmetry.Ry90_trace
#print axioms Crystallography.Symmetry.Rz90_orthogonal
#print axioms Crystallography.Symmetry.Rz90_det
#print axioms Crystallography.Symmetry.Rz90_order
#print axioms Crystallography.Symmetry.Rz90_trace
#print axioms Crystallography.Symmetry.IsSignedPerm
#print axioms Crystallography.Symmetry.Rx90_signed
#print axioms Crystallography.Symmetry.Ry90_signed
#print axioms Crystallography.Symmetry.Rz90_signed
#print axioms Crystallography.Symmetry.signedPerm_mul
#print axioms Crystallography.Symmetry.polarVector_inversion
#print axioms Crystallography.Symmetry.polarRank3_inversion
#print axioms Crystallography.Symmetry.symmetric_cubic_is_scalar
#print axioms Crystallography.Symmetry.upperTri
#print axioms Crystallography.Symmetry.upperTri_card
#print axioms Crystallography.Symmetry.eq_of_agree_on_upperTri
#print axioms Crystallography.Symmetry.voigtSwap01
#print axioms Crystallography.Symmetry.voigtSwap02
#print axioms Crystallography.Symmetry.voigtSwap12
#print axioms Crystallography.Symmetry.voigtRotZ90
#print axioms Crystallography.Symmetry.voigtRotZ90Sign
#print axioms Crystallography.Symmetry.cubicVoigt
#print axioms Crystallography.Symmetry.eq_cubicVoigt_of_voigtInvariance
#print axioms Crystallography.Symmetry.cubicVoigt_swap01
#print axioms Crystallography.Symmetry.cubicVoigt_swap02
#print axioms Crystallography.Symmetry.cubicVoigt_swap12
#print axioms Crystallography.Symmetry.cubicVoigt_rotZ90
#print axioms Crystallography.Symmetry.isotropicVoigt
#print axioms Crystallography.Symmetry.isotropicVoigt_isCubic
#print axioms Crystallography.Symmetry.isotropicVoigt_relation
#print axioms Crystallography.Symmetry.eq_isotropicVoigt_of_relation
#print axioms Crystallography.Symmetry.isotropicVoigt_swap01
#print axioms Crystallography.Symmetry.isotropicVoigt_swap02
#print axioms Crystallography.Symmetry.isotropicVoigt_swap12
#print axioms Crystallography.Symmetry.isotropicVoigt_rotZ90
#print axioms Crystallography.Symmetry.exists_symm_of_upperTri
#print axioms Crystallography.Symmetry.cubicVoigt_transpose
#print axioms Crystallography.Symmetry.cubicVoigt_inj
#print axioms Crystallography.Symmetry.isotropicVoigt_inj
#print axioms Crystallography.Symmetry.voigtIndex
#print axioms Crystallography.Symmetry.voigtFst
#print axioms Crystallography.Symmetry.voigtSnd
#print axioms Crystallography.Symmetry.voigtIndex_fst_snd
#print axioms Crystallography.Symmetry.voigtRotate
#print axioms Crystallography.Symmetry.voigtRotate_one
#print axioms Crystallography.Symmetry.voigtRotate_Rz90_transpose_apply
#print axioms Crystallography.Symmetry.Rz45
#print axioms Crystallography.Symmetry.Rz45_orthogonal
#print axioms Crystallography.Symmetry.Rz45_det
#print axioms Crystallography.Symmetry.Rz45_sq
#print axioms Crystallography.Symmetry.voigtRotate_Rz45_cubicVoigt_55
#print axioms Crystallography.Symmetry.relation_of_voigtRotate_Rz45
#print axioms Crystallography.Symmetry.eq_isotropicVoigt_of_rotationInvariance
#print axioms Crystallography.Symmetry.isotropicVoigt_voigtIndex
#print axioms Crystallography.Symmetry.voigtRotate_isotropicVoigt
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.rotMat
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.rotMat_pow5
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.rotMat_ne_one
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.c72
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.s72
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_hc
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_hs
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_order5
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_minimal
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_trace
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_trace_not_integer
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_not_latticeEndomorphism
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.R72_not_latticeSymmetry
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.doubling_latticeEndomorphism
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.doubling_not_latticeSymmetry
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.C4_latticeSymmetry
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.C6lat_latticeSymmetry
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.Rz90_latticeSymmetry
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.rank3_nonzero_not_inversionInvariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.diag123
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.diag123_symmetric
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.diag123_not_cubicInvariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_upperTri_card
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_cubicVoigt_entries
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_isotropicVoigt_instance
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_cubic_not_isotropic
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.offDiagExample
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.offDiagExample_symmetric
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.offDiagExample_not_cubicInvariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.symm_entries_agree
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter_symmetric
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter_swap01
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter_swap02
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter_swap12
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.voigtCounter_not_cubic
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_cubicVoigt_ne
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_voigtRotate_one
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_Rz45
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_Rz45_shear
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_cubic_not_Rz45_invariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_isotropic_invariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_voigtRotZ90_inverse
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_hrot_of_voigtRotate
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_cubic_Rz90_invariant
#print axioms PhyslibExtTest.CondensedMatter.Crystallography.Symmetry.test_isotropic_from_invariance
