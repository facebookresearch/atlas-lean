/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# Crystallographic symmetry: point groups and Neumann's principle

Rotation orders, concrete point-group matrices, Neumann tensor constraints, and
elastic-constant counts.

## i. Overview

A lattice endomorphism (`IsLatticeEndomorphism`) maps a full-rank lattice
into itself, possibly onto a proper sublattice, as doubling does on `ℤ`. A
lattice symmetry (`IsLatticeSymmetry`) maps a full-rank lattice onto itself,
which is what an element of the lattice's point group does. Every lattice
symmetry is a lattice endomorphism, and a lattice endomorphism of finite order
is a lattice symmetry, since `R ^ k = 1` makes `R` bijective on the lattice. So
for a rotation of finite order, the lattice hypothesis of the restriction
theorems says exactly that the rotation lies in the point group of a full-rank
lattice. Such a rotation has restricted order: combining
trace integrality (the trace is conjugation-invariant, so it equals the trace
of an integer matrix) with the rotation trace formula forces the order into
`{1, 2, 3, 4, 6}`. The two-dimensional case is proved by elementary matrix
algebra from the `2 × 2` Cayley-Hamilton identity; the three-dimensional case
reduces to it on the plane orthogonal to the rotation axis. The module then
verifies concrete point-group matrices by computation, derives Neumann's
principle consequences (inversion kills polar vectors and rank-3 polar tensors;
cubic symmetry forces a symmetric rank-2 tensor to be scalar), and counts
independent elastic constants (`21` triclinic, `3` cubic, `2` isotropic) in
Voigt notation. The isotropic count is derived from rotational invariance:
`voigtRotate` is the action of a `3 × 3` matrix on Voigt matrices through the
rank-four elasticity tensor, invariance of a cubic matrix under the `45°`
rotation `Rz45` about `z` forces `c11 - c12 = 2 * c44`, and the resulting Lamé
family is invariant under every orthogonal matrix.

Reuse-verified against Mathlib / ATLAS main: this module imports no next-50
prerequisite module.

The complete 10 plane / 32 spatial crystallographic-point-group classification
is a reference dataset, not a newly proved theorem. This module verifies
concrete matrices for selected groups only.

Neumann invariance is a physical modelling premise (a tensor property of a
crystal is invariant under the crystal's point group), carried as explicit
equations; the theorems are mathematical consequences of those hypotheses.
Neumann gives necessary (not sufficient) symmetry constraints; physical property
existence is separate and is NOT claimed here.

This module treats polar tensors only. Axial (pseudo) tensors pick up an extra
`det R` sign under improper rotations and are not covered by the polar lemmas.

## ii. Key results

- `Crystallography.Symmetry.IsLatticeEndomorphism` : a matrix conjugate to an
  integer matrix, which maps a full-rank lattice into itself.
- `Crystallography.Symmetry.trace_integer_of_latticeEndomorphism` : its trace
  is an integer.
- `Crystallography.Symmetry.basisLattice`, `isLatticeEndomorphism_iff_mapsTo`,
  `IsLatticeSymmetry` : the lattice of a basis matrix, the characterization of
  lattice endomorphisms as maps of a full-rank lattice into itself, and a
  matrix mapping a full-rank lattice onto itself.
- `Crystallography.Symmetry.IsLatticeSymmetry.isLatticeEndomorphism`,
  `IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one` : every lattice
  symmetry is a lattice endomorphism, and a finite-order lattice endomorphism
  is a lattice symmetry.
- `Crystallography.Symmetry.exists_angle_of_trace_two`,
  `Crystallography.Symmetry.exists_angle_of_trace_three` : rotation trace
  formulas.
- `Crystallography.Symmetry.crystallographic_restriction_two`,
  `Crystallography.Symmetry.crystallographic_restriction_three` : a
  finite-order rotation that is a lattice endomorphism, equivalently a lattice
  symmetry, has order in `{1, 2, 3, 4, 6}`.
- `Crystallography.Symmetry.C2`, `C4`, `mirror`, `Rx90`, `Ry90`, `Rz90` :
  concrete point-group matrices with verified orthogonality, determinant,
  order, and trace.
- `Crystallography.Symmetry.C6lat` : the six-fold rotation in the hexagonal
  lattice basis, with verified determinant, order, and trace. It is an integer
  lattice-basis matrix, not an orthogonal one.
- `Crystallography.Symmetry.IsSignedPerm`, `signedPerm_mul` : signed
  permutation matrices and closure under multiplication.
- `Crystallography.Symmetry.polarVector_inversion`,
  `polarRank3_inversion`, `symmetric_cubic_is_scalar` : Neumann consequences.
- `Crystallography.Symmetry.upperTri`, `upperTri_card`,
  `eq_of_agree_on_upperTri`, `exists_symm_of_upperTri` : 21 independent
  triclinic constants.
- `Crystallography.Symmetry.cubicVoigt`, `eq_cubicVoigt_of_voigtInvariance`,
  `cubicVoigt_inj` : the 3-parameter cubic family.
- `Crystallography.Symmetry.voigtRotate`, `voigtRotate_Rz90_transpose_apply`,
  `Rz45` : the action of a `3 × 3` matrix on Voigt matrices, which gives the
  quarter-turn entry equations of `eq_cubicVoigt_of_voigtInvariance` for
  `Rz90ᵀ`, and the `45°` rotation about `z`.
- `Crystallography.Symmetry.isotropicVoigt`,
  `eq_isotropicVoigt_of_rotationInvariance`, `voigtRotate_isotropicVoigt`,
  `isotropicVoigt_inj` : the 2-parameter Lamé family, forced by invariance
  under the axis swaps, the `z` quarter-turn and `Rz45`, and invariant under
  every orthogonal matrix.

## iii. Table of contents

- A. Lattice endomorphisms, lattice symmetries, and trace integrality
- B. The two-dimensional restriction
- C. The three-dimensional restriction by planar reduction
- D. Point groups: concrete matrices
- E. Neumann: inversion and cubic invariance
- F. Independent elastic constants

## iv. References

* MIT OCW 3.012 *Fundamentals of Materials Science*, Fall 2005, for Neumann's
  principle and tensor properties.
* J. F. Nye, *Physical Properties of Crystals*, Oxford University Press (1957),
  for Neumann's principle and tensor properties.
* DoITPoMS TLP Library, "Introduction to Anisotropy", for elastic-constant
  counts.

-/

@[expose] public section

open scoped Matrix

namespace Crystallography.Symmetry

/-! ## A. Lattice endomorphisms, lattice symmetries, and trace integrality -/

/-- A matrix is a lattice endomorphism if it is conjugate (over `ℝ`) to an
integer matrix: `R = P * M * P⁻¹` with `P` invertible. Equivalently
(`isLatticeEndomorphism_iff_mapsTo`), `R` maps the full-rank lattice
`basisLattice n P` into itself, possibly onto a proper sublattice: for `n = 1`,
`R = M = 2` and `P = 1` send `ℤ` onto `2ℤ`. A matrix mapping a full-rank
lattice onto itself is an `IsLatticeSymmetry`. -/
def IsLatticeEndomorphism (n : ℕ) (R : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, ∃ P : Matrix (Fin n) (Fin n) ℝ,
    IsUnit P.det ∧ R = P * (M.map Int.cast) * P⁻¹

/-- Trace integrality: a lattice endomorphism has integer trace, since the
trace is invariant under conjugation. -/
lemma trace_integer_of_latticeEndomorphism (n : ℕ) (R : Matrix (Fin n) (Fin n) ℝ)
    (h : IsLatticeEndomorphism n R) : ∃ k : ℤ, R.trace = k := by
  obtain ⟨M, P, hP, rfl⟩ := h
  refine ⟨M.trace, ?_⟩
  have hcyc : (P * (M.map Int.cast) * P⁻¹).trace = (M.map Int.cast).trace := by
    rw [show P * (M.map Int.cast) * P⁻¹ = (P * M.map Int.cast) * P⁻¹ from rfl,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
      Matrix.one_mul]
  rw [hcyc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, Int.cast_sum]

/-- Trace integrality in two dimensions. -/
lemma trace_integer_two (R : Matrix (Fin 2) (Fin 2) ℝ)
    (h : IsLatticeEndomorphism 2 R) : ∃ k : ℤ, R.trace = k :=
  trace_integer_of_latticeEndomorphism 2 R h

/-- Trace integrality in three dimensions. -/
lemma trace_integer_three (R : Matrix (Fin 3) (Fin 3) ℝ)
    (h : IsLatticeEndomorphism 3 R) : ∃ k : ℤ, R.trace = k :=
  trace_integer_of_latticeEndomorphism 3 R h

/-- The lattice with basis matrix `P`: the integer combinations `P *ᵥ z`,
`z : Fin n → ℤ`, of the columns of `P`. It has full rank when `P` is
invertible. -/
def basisLattice (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  Set.range fun z : Fin n → ℤ => P *ᵥ fun i => (z i : ℝ)

/-- A matrix is a lattice symmetry if it maps a full-rank lattice onto itself:
for some invertible basis matrix `P`, the image of `basisLattice n P` under `R`
is `basisLattice n P`. This is the defining property of the elements of a
lattice's point group; `IsLatticeEndomorphism` only asks for a map into the
lattice. -/
def IsLatticeSymmetry (n : ℕ) (R : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧
    (fun v => R *ᵥ v) '' basisLattice n P = basisLattice n P

/-- A matrix is a lattice endomorphism exactly when it maps some full-rank
lattice into itself: in a basis of that lattice it acts by an integer matrix. -/
theorem isLatticeEndomorphism_iff_mapsTo {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} :
    IsLatticeEndomorphism n R ↔ ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧
      Set.MapsTo (fun v => R *ᵥ v) (basisLattice n P) (basisLattice n P) := by
  constructor
  · rintro ⟨M, P, hP, hR⟩
    have hRP : R * P = P * M.map Int.cast := by
      rw [hR, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨P, hP, ?_⟩
    rintro _ ⟨z, rfl⟩
    refine ⟨M *ᵥ z, ?_⟩
    change (P *ᵥ fun i => ((M *ᵥ z) i : ℝ)) = R *ᵥ (P *ᵥ fun i => (z i : ℝ))
    rw [Matrix.mulVec_mulVec, hRP, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · rintro ⟨P, hP, hmaps⟩
    have hcol : ∀ j, ∃ m : Fin n → ℤ,
        (P *ᵥ fun i => (m i : ℝ)) = R *ᵥ (P *ᵥ Pi.single j 1) := by
      intro j
      have hcast : (fun i => ((Pi.single j 1 : Fin n → ℤ) i : ℝ)) = Pi.single j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      have hmem : P *ᵥ Pi.single j 1 ∈ basisLattice n P := by
        refine ⟨Pi.single j 1, ?_⟩
        change (P *ᵥ fun i => ((Pi.single j 1 : Fin n → ℤ) i : ℝ)) = P *ᵥ Pi.single j 1
        rw [hcast]
      exact hmaps hmem
    choose m hm using hcol
    refine ⟨Matrix.of fun i j => m j i, P, hP, ?_⟩
    have hRP : R * P = P * (Matrix.of fun i j => m j i).map Int.cast := by
      ext i j
      have e := congrFun (hm j) i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at e
      rw [← Matrix.col_apply (R * P) j i, ← e]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    calc R = R * P * P⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = P * (Matrix.of fun i j => m j i).map Int.cast * P⁻¹ := by rw [hRP]

/-- Every lattice symmetry is a lattice endomorphism. -/
theorem IsLatticeSymmetry.isLatticeEndomorphism {n : ℕ}
    {R : Matrix (Fin n) (Fin n) ℝ} (h : IsLatticeSymmetry n R) :
    IsLatticeEndomorphism n R := by
  obtain ⟨P, hP, hL⟩ := h
  refine isLatticeEndomorphism_iff_mapsTo.mpr ⟨P, hP, fun v hv => ?_⟩
  rw [← hL]
  exact Set.mem_image_of_mem _ hv

/-- A lattice endomorphism of finite order is a lattice symmetry: `R ^ k = 1`
with `0 < k` makes `R` bijective on the lattice, with inverse `R ^ (k - 1)`.
With `IsLatticeSymmetry.isLatticeEndomorphism`, the finite-order lattice
endomorphisms are exactly the finite-order lattice symmetries, so for a rotation
of finite order the lattice hypothesis of `crystallographic_restriction_two` and
`crystallographic_restriction_three` says exactly that it lies in the point
group of a full-rank lattice. -/
theorem IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one {n : ℕ}
    {R : Matrix (Fin n) (Fin n) ℝ} (h : IsLatticeEndomorphism n R) {k : ℕ}
    (hk : 0 < k) (hpow : R ^ k = 1) : IsLatticeSymmetry n R := by
  obtain ⟨P, hP, hmaps⟩ := isLatticeEndomorphism_iff_mapsTo.mp h
  have hpowmaps : ∀ j : ℕ, ∀ v ∈ basisLattice n P, (R ^ j) *ᵥ v ∈ basisLattice n P := by
    intro j
    induction j with
    | zero => intro v hv; simpa using hv
    | succ j ih =>
        intro v hv
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih _ (hmaps hv)
  refine ⟨P, hP, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hmaps hv
  · intro v hv
    refine ⟨(R ^ (k - 1)) *ᵥ v, hpowmaps _ v hv, ?_⟩
    simp only [Matrix.mulVec_mulVec, ← pow_succ', Nat.sub_add_cancel hk, hpow,
      Matrix.one_mulVec]

/-! ## B. The two-dimensional restriction -/

/-- A least exponent giving `1` divides every exponent giving `1`. -/
private lemma pow_order_dvd (M : Type*) [Monoid M] (a : M) (n k : ℕ)
    (hpos : 0 < n) (hpow : a ^ n = 1)
    (hmin : ∀ m : ℕ, 0 < m → m < n → a ^ m ≠ 1) (hk : a ^ k = 1) :
    n ∣ k := by
  have hpow2 : (a ^ n) ^ (k / n) * a ^ (k % n) = a ^ k := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hmod : a ^ (k % n) = 1 := by
    have h1 : (a ^ n) ^ (k / n) * a ^ (k % n) = 1 := by rw [hpow2]; exact hk
    rw [hpow, one_pow, one_mul] at h1
    exact h1
  by_cases hr : k % n = 0
  · exact Nat.dvd_of_mod_eq_zero hr
  · exact absurd hmod (hmin (k % n) (Nat.pos_of_ne_zero hr) (Nat.mod_lt k hpos))

/-- Case split on `Fin 2` with `OfNat` indices. -/
private lemma split2 (P : Fin 2 → Prop) : (∀ i, P i) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i; fin_cases i <;> assumption

/-- Case split on `Fin 3` with `OfNat` indices. -/
private lemma split3 (P : Fin 3 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption

/-- Case split on `Fin 6` with `OfNat` indices. -/
private lemma split6 (P : Fin 6 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i; fin_cases i <;> assumption

/-- The `2 × 2` Cayley-Hamilton identity at determinant one:
`R^2 = trace(R) • R - 1`. -/
private lemma sq_two_of_det_eq_one (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : R.det = 1) : R ^ 2 = R.trace • R - 1 := by
  rw [Matrix.det_fin_two] at hdet
  refine Matrix.ext ?_
  simp only [split2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.trace, Matrix.diag_apply] <;>
    linarith [hdet]

/-- Column-norm equations from two-dimensional orthogonality. -/
private lemma col_norm_two_of_orthogonal (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) :
    R 0 0 * R 0 0 + R 1 0 * R 1 0 = 1 ∧
    R 0 1 * R 0 1 + R 1 1 * R 1 1 = 1 := by
  have h00 : (Rᵀ * R) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) horth
  have h11 : (Rᵀ * R) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) horth
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h00 h11
  exact ⟨h00, h11⟩

/-- Diagonal entries of a `2 × 2` orthogonal matrix are bounded by one. -/
private lemma diag_abs_two_of_orthogonal (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) : |R 0 0| ≤ 1 ∧ |R 1 1| ≤ 1 := by
  obtain ⟨h00, h11⟩ := col_norm_two_of_orthogonal R horth
  have b0 : |R 0 0| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    linarith [h00, sq_nonneg (R 1 0)]
  have b1 : |R 1 1| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    linarith [h11, sq_nonneg (R 0 1)]
  exact ⟨b0, b1⟩

/-- The trace bound for `2 × 2` orthogonal matrices. -/
private lemma abs_trace_two_of_orthogonal (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) : |R.trace| ≤ 2 := by
  obtain ⟨b0, b1⟩ := diag_abs_two_of_orthogonal R horth
  have htr : R.trace = R 0 0 + R 1 1 := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [htr]
  calc |R 0 0 + R 1 1| ≤ |R 0 0| + |R 1 1| := abs_add_le _ _
    _ ≤ 1 + 1 := by linarith [b0, b1]
    _ = 2 := by norm_num

/-- Number-theoretic core of the two-dimensional crystallographic restriction:
an orthogonal `2 × 2` matrix of determinant one, integer trace, and finite
order `n` has `n ∈ {1, 2, 3, 4, 6}`. -/
private lemma order_two_core (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) (hdet : R.det = 1)
    (htrace : ∃ k : ℤ, R.trace = k)
    (n : ℕ) (hpos : 0 < n) (hpow : R ^ n = 1)
    (hmin : ∀ m : ℕ, 0 < m → m < n → R ^ m ≠ 1) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have hbound := abs_trace_two_of_orthogonal R horth
  have hsq := sq_two_of_det_eq_one R hdet
  have tr1 : (1 : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  have htr : R.trace = R 0 0 + R 1 1 := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  obtain ⟨k, hk⟩ := htrace
  have hkbound : -2 ≤ k ∧ k ≤ 2 := by
    have hcc : ((|k| : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      norm_num
      rw [← hk]
      exact hbound
    have habs : |k| ≤ 2 := by exact_mod_cast hcc
    exact abs_le.mp habs
  obtain ⟨hklo, hkhi⟩ := hkbound
  interval_cases k <;> push_cast at hk
  · -- trace -2: R = -1, so n = 2
    obtain ⟨h00, h11⟩ := col_norm_two_of_orthogonal R horth
    obtain ⟨b0, b1⟩ := diag_abs_two_of_orthogonal R horth
    have hsum : R 0 0 + R 1 1 = -2 := by rw [← htr, hk]
    have g0 := (abs_le.mp b0).1
    have g1 := (abs_le.mp b1).1
    have ha : R 0 0 = -1 := by linarith [hsum]
    have hd : R 1 1 = -1 := by linarith [hsum]
    have hc0 : R 1 0 * R 1 0 = 0 := by rw [ha] at h00; linear_combination h00
    have hc : R 1 0 = 0 := mul_self_eq_zero.mp hc0
    have hb0 : R 0 1 * R 0 1 = 0 := by rw [hd] at h11; linear_combination h11
    have hb : R 0 1 = 0 := mul_self_eq_zero.mp hb0
    have hR : R = -1 := by
      refine Matrix.ext ?_
      simp only [split2]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [ha, hd, hb, hc, Matrix.neg_apply]
    have h2pow : R ^ 2 = 1 := by rw [hR, pow_two, neg_mul_neg, one_mul]
    have hdvd : n ∣ 2 := pow_order_dvd _ _ _ _ hpos hpow hmin h2pow
    have h1n : 1 ≤ n := hpos
    have h2n : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · rw [pow_one] at hpow; rw [hpow, tr1] at hk; norm_num at hk
    · decide
  · -- trace -1: order 3
    have h2 : R ^ 2 = -R - 1 := by
      rw [hk] at hsq; rwa [neg_smul, one_smul] at hsq
    have h3 : R ^ 3 = 1 := by
      have e3 : R ^ 3 = R ^ 2 * R := pow_succ R 2
      rw [e3, h2, sub_mul, neg_mul, one_mul, ← pow_two, h2]
      abel
    have hdvd : n ∣ 3 := pow_order_dvd _ _ _ _ hpos hpow hmin h3
    have h1n : 1 ≤ n := hpos
    have h3n : n ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · rw [pow_one] at hpow; rw [hpow, tr1] at hk; norm_num at hk
    · have htr2 : (R ^ 2).trace = 2 := by rw [hpow]; exact tr1
      rw [h2, Matrix.trace_sub, Matrix.trace_neg, hk, tr1] at htr2
      norm_num at htr2
    · decide
  · -- trace 0: order 4
    have h2 : R ^ 2 = -1 := by
      rw [hk] at hsq
      simpa [zero_smul, zero_sub] using hsq
    have h4 : R ^ 4 = 1 := by
      have e4 : R ^ 4 = (R ^ 2) ^ 2 := pow_mul R 2 2
      rw [e4, h2, pow_two, neg_mul_neg, one_mul]
    have h3 : R ^ 3 = -R := by
      have e3 : R ^ 3 = R ^ 2 * R := pow_succ R 2
      rw [e3, h2, neg_mul, one_mul]
    have hdvd : n ∣ 4 := pow_order_dvd _ _ _ _ hpos hpow hmin h4
    have h1n : 1 ≤ n := hpos
    have h4n : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · rw [pow_one] at hpow; rw [hpow, tr1] at hk; norm_num at hk
    · have htr2 : (R ^ 2).trace = 2 := by rw [hpow]; exact tr1
      rw [h2, Matrix.trace_neg, tr1] at htr2
      norm_num at htr2
    · have htr3 : (R ^ 3).trace = 2 := by rw [hpow]; exact tr1
      rw [h3, Matrix.trace_neg, hk] at htr3
      norm_num at htr3
    · decide
  · -- trace 1: order 6
    have h2 : R ^ 2 = R - 1 := by
      rw [hk] at hsq
      simpa [one_smul] using hsq
    have h3 : R ^ 3 = -1 := by
      have e3 : R ^ 3 = R ^ 2 * R := pow_succ R 2
      rw [e3, h2, sub_mul, one_mul, ← pow_two, h2]
      abel
    have h6 : R ^ 6 = 1 := by
      have e6 : R ^ 6 = (R ^ 3) ^ 2 := pow_mul R 3 2
      rw [e6, h3, pow_two, neg_mul_neg, one_mul]
    have h4 : R ^ 4 = -R := by
      have e4 : R ^ 4 = R ^ 3 * R := pow_succ R 3
      rw [e4, h3, neg_mul, one_mul]
    have h5 : R ^ 5 = 1 - R := by
      have e5 : R ^ 5 = R ^ 4 * R := pow_succ R 4
      rw [e5, h4, neg_mul, ← pow_two, h2, neg_sub]
    have hdvd : n ∣ 6 := pow_order_dvd _ _ _ _ hpos hpow hmin h6
    have h1n : 1 ≤ n := hpos
    have h6n : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · rw [pow_one] at hpow; rw [hpow, tr1] at hk; norm_num at hk
    · have htr2 : (R ^ 2).trace = 2 := by rw [hpow]; exact tr1
      rw [h2, Matrix.trace_sub, tr1, hk] at htr2
      norm_num at htr2
    · have htr3 : (R ^ 3).trace = 2 := by rw [hpow]; exact tr1
      rw [h3, Matrix.trace_neg, tr1] at htr3
      norm_num at htr3
    · have htr4 : (R ^ 4).trace = 2 := by rw [hpow]; exact tr1
      rw [h4, Matrix.trace_neg, hk] at htr4
      norm_num at htr4
    · have htr5 : (R ^ 5).trace = 2 := by rw [hpow]; exact tr1
      rw [h5, Matrix.trace_sub, tr1, hk] at htr5
      norm_num at htr5
    · decide
  · -- trace 2: R = 1, so n = 1
    obtain ⟨h00, h11⟩ := col_norm_two_of_orthogonal R horth
    obtain ⟨b0, b1⟩ := diag_abs_two_of_orthogonal R horth
    have hsum : R 0 0 + R 1 1 = 2 := by rw [← htr, hk]
    have g0 := (abs_le.mp b0).2
    have g1 := (abs_le.mp b1).2
    have ha : R 0 0 = 1 := by linarith [hsum]
    have hd : R 1 1 = 1 := by linarith [hsum]
    have hc0 : R 1 0 * R 1 0 = 0 := by rw [ha] at h00; linear_combination h00
    have hc : R 1 0 = 0 := mul_self_eq_zero.mp hc0
    have hb0 : R 0 1 * R 0 1 = 0 := by rw [hd] at h11; linear_combination h11
    have hb : R 0 1 = 0 := mul_self_eq_zero.mp hb0
    have hR : R = 1 := by
      refine Matrix.ext ?_
      simp only [split2]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [ha, hd, hb, hc]
    have h1pow : R ^ 1 = 1 := by rw [pow_one, hR]
    have hdvd : n ∣ 1 := pow_order_dvd _ _ _ _ hpos hpow hmin h1pow
    have hn1 : n = 1 := Nat.dvd_one.mp hdvd
    rw [hn1]
    decide

/-- Two-dimensional rotation trace formula: an orthogonal `2 × 2` matrix of
determinant one has trace `2 cos θ` for some angle `θ ∈ [0, π]`. -/
lemma exists_angle_of_trace_two (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) (_hdet : R.det = 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧ R.trace = 2 * Real.cos θ := by
  have hbound := abs_trace_two_of_orthogonal R horth
  have h1 : -1 ≤ R.trace / 2 := by
    have g := (abs_le.mp hbound).1
    linarith
  have h2 : R.trace / 2 ≤ 1 := by
    have g := (abs_le.mp hbound).2
    linarith
  refine ⟨Real.arccos (R.trace / 2), Real.arccos_nonneg _,
    Real.arccos_le_pi _, ?_⟩
  have hcos := Real.cos_arccos h1 h2
  linarith [hcos]

/-- The two-dimensional crystallographic restriction: a proper rotation of
finite order `n` that is a lattice endomorphism has `n ∈ {1, 2, 3, 4, 6}`. For
a matrix of finite order, being a lattice endomorphism is equivalent to being a
lattice symmetry (`IsLatticeEndomorphism.isLatticeSymmetry_of_pow_eq_one`,
`IsLatticeSymmetry.isLatticeEndomorphism`), so this bounds the orders of the
rotations in the point group of a planar lattice. -/
theorem crystallographic_restriction_two (R : Matrix (Fin 2) (Fin 2) ℝ)
    (horth : Rᵀ * R = 1) (hdet : R.det = 1)
    (hlat : IsLatticeEndomorphism 2 R)
    (n : ℕ) (hpos : 0 < n) (hpow : R ^ n = 1)
    (hmin : ∀ m : ℕ, 0 < m → m < n → R ^ m ≠ 1) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) :=
  order_two_core R horth hdet (trace_integer_two R hlat) n hpos hpow hmin

/-! ## C. The three-dimensional restriction by planar reduction -/

/-- The matrix with columns `x`, `y`, `z`. -/
private def mkOrtho (x y z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if j = 0 then x i else if j = 1 then y i else z i

/-- A matrix with orthonormal columns is orthogonal. -/
private lemma orthonormal_columns (x y z : Fin 3 → ℝ)
    (hxx : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = 1)
    (hyy : y 0 * y 0 + y 1 * y 1 + y 2 * y 2 = 1)
    (hzz : z 0 * z 0 + z 1 * z 1 + z 2 * z 2 = 1)
    (hxy : x 0 * y 0 + x 1 * y 1 + x 2 * y 2 = 0)
    (hxz : x 0 * z 0 + x 1 * z 1 + x 2 * z 2 = 0)
    (hyz : y 0 * z 0 + y 1 * z 1 + y 2 * z 2 = 0) :
    (mkOrtho x y z)ᵀ * mkOrtho x y z = 1 ∧
    mkOrtho x y z * (mkOrtho x y z)ᵀ = 1 := by
  have q0 : ∀ i, mkOrtho x y z i 0 = x i := fun i => rfl
  have q1 : ∀ i, mkOrtho x y z i 1 = y i := fun i => rfl
  have q2 : ∀ i, mkOrtho x y z i 2 = z i := fun i => rfl
  have hQQ : (mkOrtho x y z)ᵀ * mkOrtho x y z = 1 := by
    refine Matrix.ext ?_
    simp only [split3]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        q0, q1, q2] <;>
      linarith [hxx, hyy, hzz, hxy, hxz, hyz]
  refine ⟨hQQ, ?_⟩
  exact (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp hQQ

/-- Every unit vector in `Fin 3 → ℝ` extends to an orthonormal basis: there is
an orthogonal matrix with first column `u`. -/
private lemma orthonormal_completion (u : Fin 3 → ℝ)
    (hunit : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ,
      Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧ ∀ i, Q i 0 = u i := by
  by_cases hS : u 0 * u 0 + u 1 * u 1 = 0
  · -- Case B: u is ±e₂; complete with e₀, e₁.
    have hnn0 : 0 ≤ u 0 * u 0 := mul_self_nonneg _
    have hnn1 : 0 ≤ u 1 * u 1 := mul_self_nonneg _
    rw [add_eq_zero_iff_of_nonneg hnn0 hnn1] at hS
    obtain ⟨hu00, hu11⟩ := hS
    have hu0 : u 0 = 0 := mul_self_eq_zero.mp hu00
    have hu1 : u 1 = 0 := mul_self_eq_zero.mp hu11
    have hyy : (1 : ℝ) * 1 + 0 * 0 + 0 * 0 = 1 := by norm_num
    have hzz : (0 : ℝ) * 0 + 1 * 1 + 0 * 0 = 1 := by norm_num
    have hxy : u 0 * 1 + u 1 * 0 + u 2 * 0 = 0 := by rw [hu0]; ring
    have hxz : u 0 * 0 + u 1 * 1 + u 2 * 0 = 0 := by rw [hu1]; ring
    have hyz : (1 : ℝ) * 0 + 0 * 1 + 0 * 0 = 0 := by norm_num
    refine ⟨mkOrtho u ![1, 0, 0] ![0, 1, 0],
      (orthonormal_columns u ![1, 0, 0] ![0, 1, 0]
        hunit hyy hzz hxy hxz hyz).1,
      (orthonormal_columns u ![1, 0, 0] ![0, 1, 0]
        hunit hyy hzz hxy hxz hyz).2,
      fun i => rfl⟩
  · -- Case A: (u₀, u₁) ≠ 0; use v = (-u₁, u₀, 0)/r, w = u × v.
    have hle : 0 ≤ u 0 * u 0 + u 1 * u 1 :=
      add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have hSpos : 0 < u 0 * u 0 + u 1 * u 1 :=
      lt_of_not_ge (fun hge => hS (le_antisymm hge hle))
    obtain ⟨r, hr2, hrpos⟩ : ∃ r : ℝ,
        r ^ 2 = u 0 * u 0 + u 1 * u 1 ∧ 0 < r :=
      ⟨Real.sqrt _, Real.sq_sqrt hle, Real.sqrt_pos.mpr hSpos⟩
    have hr_ne : r ≠ 0 := ne_of_gt hrpos
    have hr2ne : r ^ 2 ≠ 0 := by rw [hr2]; exact hS
    have key_v : u 1 * u 1 + u 0 * u 0 = r ^ 2 := by
      linear_combination -hr2
    have key_w : (u 2 * u 0) * (u 2 * u 0) + (u 2 * u 1) * (u 2 * u 1) +
        r ^ 2 * r ^ 2 = r ^ 2 := by
      linear_combination (u 0 * u 0 + u 1 * u 1) * hunit +
        (r ^ 2 + (u 0 * u 0 + u 1 * u 1) - 1) * hr2
    have hyy : (-(u 1) / r) * (-(u 1) / r) + ((u 0) / r) * ((u 0) / r) +
        0 * 0 = 1 := by
      rw [← pow_two, ← pow_two, div_pow, div_pow, mul_zero, add_zero,
        ← add_div, div_eq_iff hr2ne]
      linear_combination key_v
    have hzz : (-(u 2) * (u 0) / r) * (-(u 2) * (u 0) / r) +
        (-(u 2) * (u 1) / r) * (-(u 2) * (u 1) / r) + r * r = 1 := by
      rw [← pow_two, ← pow_two, div_pow, div_pow, ← add_div]
      have e : ((-(u 2) * (u 0)) ^ 2 + (-(u 2) * (u 1)) ^ 2) / r ^ 2 =
          1 - r * r := by
        rw [div_eq_iff hr2ne]
        linear_combination key_w
      rw [e]
      ring
    have hxy : u 0 * (-(u 1) / r) + u 1 * ((u 0) / r) + u 2 * 0 = 0 := by
      rw [← mul_div_assoc, ← mul_div_assoc, mul_zero, add_zero,
        ← add_div, div_eq_iff hr_ne]
      ring
    have hxz : u 0 * (-(u 2) * (u 0) / r) + u 1 * (-(u 2) * (u 1) / r) +
        u 2 * r = 0 := by
      rw [← mul_div_assoc, ← mul_div_assoc]
      have e : (u 0 * (-(u 2) * (u 0)) + u 1 * (-(u 2) * (u 1))) / r =
          -(u 2 * r) := by
        rw [div_eq_iff hr_ne]
        linear_combination u 2 * hr2
      rw [← add_div, e]
      ring
    have hyz : (-(u 1) / r) * (-(u 2) * (u 0) / r) +
        ((u 0) / r) * (-(u 2) * (u 1) / r) + 0 * r = 0 := by
      rw [div_mul_div_comm, div_mul_div_comm, zero_mul, add_zero,
        ← add_div, div_eq_iff (mul_ne_zero hr_ne hr_ne)]
      ring
    refine ⟨mkOrtho u ![-(u 1) / r, (u 0) / r, 0]
        ![-(u 2) * (u 0) / r, -(u 2) * (u 1) / r, r],
      (orthonormal_columns u _ _ hunit hyy hzz hxy hxz hyz).1,
      (orthonormal_columns u _ _ hunit hyy hzz hxy hxz hyz).2,
      fun i => rfl⟩

/-- The `2 × 2` planar block of a `3 × 3` matrix fixing `e₀`. -/
private def planarSub (P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![P 1 1, P 1 2; P 2 1, P 2 2]

/-- The planar block of an orthogonal matrix fixing `e₀` is orthogonal. -/
private lemma planar_orth (P : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : Pᵀ * P = 1)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) :
    (planarSub P)ᵀ * planarSub P = 1 := by
  have o11 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have o22 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 = 1 := Matrix.one_apply_eq 2
  have o12 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o21 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o01 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o02 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 :=
    Matrix.one_apply_ne (by decide)
  have r01 : P 0 1 = 0 := by rw [hrow 1]; exact o01
  have r02 : P 0 2 = 0 := by rw [hrow 2]; exact o02
  have q11 : P 1 1 * P 1 1 + P 2 1 * P 2 1 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      r01, o11, mul_zero] at h
    linear_combination h
  have q12 : P 1 1 * P 1 2 + P 2 1 * P 2 2 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      r01, r02, o12, mul_zero] at h
    linear_combination h
  have q21 : P 1 2 * P 1 1 + P 2 2 * P 2 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 1) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      r01, r02, o21, mul_zero] at h
    linear_combination h
  have q22 : P 1 2 * P 1 2 + P 2 2 * P 2 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      r02, o22, mul_zero] at h
    linear_combination h
  have t00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have t11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have t01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  have t10 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 :=
    Matrix.one_apply_ne (by decide)
  refine Matrix.ext ?_
  simp only [split2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      planarSub, Matrix.of_apply, t00]
    exact q11
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      planarSub, Matrix.of_apply, t01]
    exact q12
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      planarSub, Matrix.of_apply, t10]
    exact q21
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      planarSub, Matrix.of_apply, t11]
    exact q22

/-- The planar block of a determinant-one matrix fixing `e₀` has determinant
one. -/
private lemma planar_det (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hdetP : P.det = 1)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) :
    (planarSub P).det = 1 := by
  have o00 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have o01 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o02 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 :=
    Matrix.one_apply_ne (by decide)
  have r00 : P 0 0 = 1 := by rw [hrow 0]; exact o00
  have r01 : P 0 1 = 0 := by rw [hrow 1]; exact o01
  have r02 : P 0 2 = 0 := by rw [hrow 2]; exact o02
  rw [Matrix.det_fin_three] at hdetP
  rw [r00, r01, r02] at hdetP
  rw [Matrix.det_fin_two]
  simp only [planarSub, Matrix.of_apply]
  show P 1 1 * P 2 2 - P 1 2 * P 2 1 = 1
  linear_combination hdetP

/-- The planar block's trace is the full trace minus one. -/
private lemma planar_trace (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) :
    (planarSub P).trace = P.trace - 1 := by
  have o00 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have r00 : P 0 0 = 1 := by rw [hrow 0]; exact o00
  have eS : (planarSub P).trace = P 1 1 + P 2 2 := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, planarSub,
      Matrix.of_apply]
  have eP : P.trace = P 0 0 + P 1 1 + P 2 2 := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  rw [eS, eP, r00]
  ring

/-- Block-diagonal embedding of a `2 × 2` matrix into a `3 × 3` matrix fixing
`e₀`. -/
private def blockMat (T : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, T 0 0, T 0 1; 0, T 1 0, T 1 1]

/-- The block embedding preserves `1`. -/
private lemma blockMat_one : blockMat 1 = 1 := by
  refine Matrix.ext ?_
  simp only [split3]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp [blockMat, Matrix.of_apply]

/-- The block embedding reflects `1`. -/
private lemma blockMat_eq_one (T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : blockMat T = 1) : T = 1 := by
  refine Matrix.ext ?_
  simp only [split2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) hT
    simpa [blockMat, Matrix.of_apply] using h
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hT
    simpa [blockMat, Matrix.of_apply] using h
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 1) hT
    simpa [blockMat, Matrix.of_apply] using h
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) hT
    simpa [blockMat, Matrix.of_apply] using h

/-- Multiplying a matrix fixing `e₀` by a block matrix multiplies the blocks. -/
private lemma blockMat_mul (P : Matrix (Fin 3) (Fin 3) ℝ)
    (T : Matrix (Fin 2) (Fin 2) ℝ)
    (hcol : ∀ i, P i 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) :
    P * blockMat T = blockMat (planarSub P * T) := by
  have o00 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have o01 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o02 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o10 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 0 :=
    Matrix.one_apply_ne (by decide)
  have o20 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0 :=
    Matrix.one_apply_ne (by decide)
  have r00 : P 0 0 = 1 := by rw [hrow 0]; exact o00
  have r01 : P 0 1 = 0 := by rw [hrow 1]; exact o01
  have r02 : P 0 2 = 0 := by rw [hrow 2]; exact o02
  have c10 : P 1 0 = 0 := by rw [hcol 1]; exact o10
  have c20 : P 2 0 = 0 := by rw [hcol 2]; exact o20
  refine Matrix.ext ?_
  simp only [split3]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      blockMat, planarSub, Matrix.of_apply, r00, r01, r02, c10, c20]

/-- Powers of a matrix fixing `e₀` are block powers. -/
private lemma planar_pow (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hcol : ∀ i, P i 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) (k : ℕ) :
    P ^ k = blockMat ((planarSub P) ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact blockMat_one.symm
  | succ k ih =>
      rw [pow_succ', pow_succ', ih]
      exact blockMat_mul P _ hcol hrow

/-- Order transfer between a matrix fixing `e₀` and its planar block. -/
private lemma planar_block (P : Matrix (Fin 3) (Fin 3) ℝ)
    (horth : Pᵀ * P = 1) (hdetP : P.det = 1)
    (hcol : ∀ i, P i 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0)
    (hrow : ∀ j, P 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      Sᵀ * S = 1 ∧ S.det = 1 ∧ S.trace = P.trace - 1 ∧
      ∀ k : ℕ, P ^ k = 1 ↔ S ^ k = 1 := by
  refine ⟨planarSub P, planar_orth P horth hrow, planar_det P hdetP hrow,
    planar_trace P hrow, ?_⟩
  intro k
  constructor
  · intro hPk
    have hblk := planar_pow P hcol hrow k
    rw [hPk] at hblk
    exact blockMat_eq_one _ hblk.symm
  · intro hSk
    have hblk := planar_pow P hcol hrow k
    rw [hSk] at hblk
    rw [hblk]
    exact blockMat_one

/-- Reduction package: the planar block of a 3D rotation about axis `u`,
with the same finite orders as `R`. -/
private lemma planar_package (R : Matrix (Fin 3) (Fin 3) ℝ)
    (horth1 : Rᵀ * R = 1) (hdetR : R.det = 1)
    (u : Fin 3 → ℝ)
    (hunit : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (haxis : R *ᵥ u = u) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      Sᵀ * S = 1 ∧ S.det = 1 ∧ S.trace = R.trace - 1 ∧
      ∀ k : ℕ, R ^ k = 1 ↔ S ^ k = 1 := by
  obtain ⟨Q, hQ, hQQ, hQ0⟩ := orthonormal_completion u hunit
  have e1 : ∀ l, (R * Q) l 0 = u l := fun l => by
    have hax := congrFun haxis l
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, hQ0] using hax
  have e2 : ∀ i, (Qᵀ * R * Q) i 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0 :=
    fun i => by
      have h1 : (Qᵀ * R * Q) i 0 = (Qᵀ * Q) i 0 := by
        rw [Matrix.mul_assoc]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, e1, hQ0]
      rw [h1, hQ]
  have hRorth : (Qᵀ * R * Q)ᵀ * (Qᵀ * R * Q) = 1 := by
    have e : (Qᵀ * R * Q)ᵀ * (Qᵀ * R * Q)
        = Qᵀ * (Rᵀ * ((Q * Qᵀ) * (R * Q))) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    rw [e, hQQ, one_mul,
      show Rᵀ * (R * Q) = Q from by
        rw [← Matrix.mul_assoc Rᵀ R Q, horth1, one_mul],
      hQ]
  have r0 : ∀ j, (Qᵀ * R * Q) 0 j = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j :=
    fun j => by
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 j) hRorth
      rw [Matrix.mul_apply] at h
      simp only [Matrix.transpose_apply, Fin.sum_univ_three] at h
      rw [e2 0, e2 1, e2 2] at h
      simp at h
      exact h
  have hdetP : (Qᵀ * R * Q).det = 1 := by
    have hq2 : Q.det * Q.det = 1 := by
      have h := congrArg Matrix.det hQ
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      exact h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetR, mul_one]
    exact hq2
  have htrP : (Qᵀ * R * Q).trace = R.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc Q Qᵀ R, hQQ, one_mul]
  have hconj : ∀ k : ℕ, (Qᵀ * R * Q) ^ k = Qᵀ * (R ^ k) * Q := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one]; exact hQ.symm
    | succ k ih =>
        rw [pow_succ', pow_succ', ih]
        have e : (Qᵀ * R * Q) * (Qᵀ * (R ^ k) * Q)
            = Qᵀ * ((R * (Q * Qᵀ)) * R ^ k) * Q := by
          simp only [Matrix.mul_assoc]
        rw [e, hQQ, mul_one]
  obtain ⟨S, hSorth, hSdet, hStr, hiff⟩ :=
    planar_block (Qᵀ * R * Q) hRorth hdetP e2 r0
  refine ⟨S, hSorth, hSdet, ?_, ?_⟩
  · rw [hStr, htrP]
  · intro k
    constructor
    · intro hRk
      have hPk : (Qᵀ * R * Q) ^ k = 1 := by
        rw [hconj k, hRk, mul_one, hQ]
      exact (hiff k).mp hPk
    · intro hSk
      have hPk : (Qᵀ * R * Q) ^ k = 1 := (hiff k).mpr hSk
      have e2r : Q * (Qᵀ * (R ^ k) * Q) * Qᵀ
          = (Q * Qᵀ) * ((R ^ k) * (Q * Qᵀ)) := by
        simp only [Matrix.mul_assoc]
      have h1 : Q * ((Qᵀ * R * Q) ^ k) * Qᵀ = R ^ k := by
        rw [hconj k, e2r, hQQ]
        simp
      rw [← h1, hPk]
      simp [hQQ]

/-- The three-dimensional crystallographic restriction, via the planar
reduction. -/
private lemma order_three_core (R : Matrix (Fin 3) (Fin 3) ℝ)
    (horth1 : Rᵀ * R = 1) (_horth2 : R * Rᵀ = 1) (hdetR : R.det = 1)
    (u : Fin 3 → ℝ)
    (hunit : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (haxis : R *ᵥ u = u)
    (htrace : ∃ k : ℤ, R.trace = k)
    (n : ℕ) (hpos : 0 < n) (hpow : R ^ n = 1)
    (hmin : ∀ m : ℕ, 0 < m → m < n → R ^ m ≠ 1) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  obtain ⟨S, hSorth, hSdet, hStr, hiff⟩ :=
    planar_package R horth1 hdetR u hunit haxis
  have htraceS : ∃ k : ℤ, S.trace = k := by
    obtain ⟨k, hk⟩ := htrace
    refine ⟨k - 1, ?_⟩
    rw [hStr, hk, Int.cast_sub, Int.cast_one]
  have hpowS : S ^ n = 1 := (hiff n).mp hpow
  have hminS : ∀ m : ℕ, 0 < m → m < n → S ^ m ≠ 1 := by
    intro m hmpos hmlt hSm
    exact hmin m hmpos hmlt ((hiff m).mpr hSm)
  exact order_two_core S hSorth hSdet htraceS n hpos hpowS hminS

/-- Three-dimensional rotation trace formula: a proper rotation with axis `u`
has trace `1 + 2 cos θ` for some angle `θ ∈ [0, π]`. -/
lemma exists_angle_of_trace_three (R : Matrix (Fin 3) (Fin 3) ℝ)
    (horth1 : Rᵀ * R = 1) (_horth2 : R * Rᵀ = 1) (hdetR : R.det = 1)
    (u : Fin 3 → ℝ)
    (hunit : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (haxis : R *ᵥ u = u) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧ R.trace = 1 + 2 * Real.cos θ := by
  obtain ⟨S, hSorth, _hSdet, hStr, _hiff⟩ :=
    planar_package R horth1 hdetR u hunit haxis
  have hbound := abs_trace_two_of_orthogonal S hSorth
  have h1 : -1 ≤ (R.trace - 1) / 2 := by
    have g := (abs_le.mp hbound).1
    rw [hStr] at g
    linarith
  have h2 : (R.trace - 1) / 2 ≤ 1 := by
    have g := (abs_le.mp hbound).2
    rw [hStr] at g
    linarith
  refine ⟨Real.arccos ((R.trace - 1) / 2), Real.arccos_nonneg _,
    Real.arccos_le_pi _, ?_⟩
  have hcos := Real.cos_arccos h1 h2
  linarith [hcos]

/-- The three-dimensional crystallographic restriction: a proper rotation with
axis `u` and finite order `n` that is a lattice endomorphism, equivalently (as
in `crystallographic_restriction_two`) a lattice symmetry, has
`n ∈ {1, 2, 3, 4, 6}`. -/
theorem crystallographic_restriction_three (R : Matrix (Fin 3) (Fin 3) ℝ)
    (horth1 : Rᵀ * R = 1) (horth2 : R * Rᵀ = 1) (hdetR : R.det = 1)
    (u : Fin 3 → ℝ)
    (hunit : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (haxis : R *ᵥ u = u)
    (hlat : IsLatticeEndomorphism 3 R)
    (n : ℕ) (hpos : 0 < n) (hpow : R ^ n = 1)
    (hmin : ∀ m : ℕ, 0 < m → m < n → R ^ m ≠ 1) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) :=
  order_three_core R horth1 horth2 hdetR u hunit haxis
    (trace_integer_three R hlat) n hpos hpow hmin

/-! ## D. Point groups: concrete matrices -/

/-- The 2D half-turn. -/
def C2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -1]

/-- The 2D quarter-turn. -/
def C4 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The order-six rotation in the hexagonal lattice basis. This is the
lattice-basis matrix with integer entries, not the Cartesian rotation. -/
def C6lat : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 0]

/-- Reflection across the x-axis (improper: determinant `-1`). -/
def mirror : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `C2` is orthogonal. -/
lemma C2_orthogonal : C2ᵀ * C2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.of_apply]

/-- `C2` has determinant one. -/
lemma C2_det : C2.det = 1 := by
  simp [C2, Matrix.det_fin_two_of]

/-- `C2` has order two. -/
lemma C2_order : C2 ^ 2 = 1 ∧ ∀ m : ℕ, 0 < m → m < 2 → C2 ^ m ≠ 1 := by
  have h2 : C2 ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C2, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  refine ⟨h2, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  intro h
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [pow_one, C2, Matrix.of_apply] at e

/-- `C2` has trace `-2`. -/
lemma C2_trace : C2.trace = -2 := by
  simp [C2, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.of_apply]
  norm_num

/-- `C4` is orthogonal. -/
lemma C4_orthogonal : C4ᵀ * C4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.of_apply]

/-- `C4` has determinant one. -/
lemma C4_det : C4.det = 1 := by
  simp [C4, Matrix.det_fin_two_of]

/-- `C4` has order four. -/
lemma C4_order : C4 ^ 4 = 1 ∧ ∀ m : ℕ, 0 < m → m < 4 → C4 ^ m ≠ 1 := by
  have h2v : C4 ^ 2 = !![-1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C4, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have h3v : C4 ^ 3 = !![0, 1; -1, 0] := by
    have e3 : C4 ^ 3 = C4 ^ 2 * C4 := pow_succ C4 2
    rw [e3, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C4, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have h4 : C4 ^ 4 = 1 := by
    have e4 : C4 ^ 4 = (C4 ^ 2) ^ 2 := pow_mul C4 2 2
    rw [e4, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  refine ⟨h4, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [pow_one, C4, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [h2v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [h3v, Matrix.of_apply] at e

/-- `C4` has trace zero. -/
lemma C4_trace : C4.trace = 0 := by
  simp [C4, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.of_apply]

/-- `C6lat` has determinant one. -/
lemma C6lat_det : C6lat.det = 1 := by
  simp [C6lat, Matrix.det_fin_two_of]

/-- `C6lat` has order six. -/
lemma C6lat_order :
    C6lat ^ 6 = 1 ∧ ∀ m : ℕ, 0 < m → m < 6 → C6lat ^ m ≠ 1 := by
  have h2v : C6lat ^ 2 = !![0, -1; 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C6lat, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply]
  have h3v : C6lat ^ 3 = !![-1, 0; 0, -1] := by
    have e3 : C6lat ^ 3 = C6lat ^ 2 * C6lat := pow_succ C6lat 2
    rw [e3, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C6lat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have h4v : C6lat ^ 4 = !![-1, 1; -1, 0] := by
    have e4 : C6lat ^ 4 = C6lat ^ 3 * C6lat := pow_succ C6lat 3
    rw [e4, h3v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C6lat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have h5v : C6lat ^ 5 = !![0, 1; -1, 1] := by
    have e5 : C6lat ^ 5 = C6lat ^ 4 * C6lat := pow_succ C6lat 4
    rw [e5, h4v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C6lat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have h6 : C6lat ^ 6 = 1 := by
    have e6 : C6lat ^ 6 = (C6lat ^ 3) ^ 2 := pow_mul C6lat 3 2
    rw [e6, h3v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  refine ⟨h6, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [pow_one, C6lat, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [h2v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [h3v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [h4v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [h5v, Matrix.of_apply] at e

/-- `C6lat` has trace one (so `2 cos θ = 1`). -/
lemma C6lat_trace : C6lat.trace = 1 := by
  simp [C6lat, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.of_apply]

/-- `mirror` is orthogonal. -/
lemma mirror_orthogonal : mirrorᵀ * mirror = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mirror, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.of_apply]

/-- `mirror` has determinant `-1` (improper). -/
lemma mirror_det : mirror.det = -1 := by
  simp [mirror, Matrix.det_fin_two_of]

/-- `mirror` has order two. -/
lemma mirror_order :
    mirror ^ 2 = 1 ∧ ∀ m : ℕ, 0 < m → m < 2 → mirror ^ m ≠ 1 := by
  have h2 : mirror ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mirror, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.of_apply]
  refine ⟨h2, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  intro h
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  norm_num [pow_one, mirror, Matrix.of_apply] at e

/-- `mirror` has trace zero. -/
lemma mirror_trace : mirror.trace = 0 := by
  simp [mirror, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.of_apply]

/-- Quarter-turn about the x-axis (cubic generator). -/
def Rx90 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -1; 0, 1, 0]

/-- Quarter-turn about the y-axis (cubic generator). -/
def Ry90 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 1, 0; -1, 0, 0]

/-- Quarter-turn about the z-axis (cubic generator). -/
def Rz90 : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- `Rx90` is orthogonal. -/
lemma Rx90_orthogonal : Rx90ᵀ * Rx90 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rx90, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.of_apply]

/-- `Rx90` has determinant one. -/
lemma Rx90_det : Rx90.det = 1 := by
  simp [Rx90, Matrix.det_fin_three]

/-- `Rx90` has order four. -/
lemma Rx90_order :
    Rx90 ^ 4 = 1 ∧ ∀ m : ℕ, 0 < m → m < 4 → Rx90 ^ m ≠ 1 := by
  have h2v : Rx90 ^ 2 = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rx90, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.of_apply]
  have h3v : Rx90 ^ 3 = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
    have e3 : Rx90 ^ 3 = Rx90 ^ 2 * Rx90 := pow_succ Rx90 2
    rw [e3, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rx90, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  have h4 : Rx90 ^ 4 = 1 := by
    have e4 : Rx90 ^ 4 = (Rx90 ^ 2) ^ 2 := pow_mul Rx90 2 2
    rw [e4, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  refine ⟨h4, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
    norm_num [pow_one, Rx90, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
    norm_num [h2v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) h
    norm_num [h3v, Matrix.of_apply] at e

/-- `Rx90` has trace one. -/
lemma Rx90_trace : Rx90.trace = 1 := by
  simp [Rx90, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three,
    Matrix.of_apply]

/-- `Ry90` is orthogonal. -/
lemma Ry90_orthogonal : Ry90ᵀ * Ry90 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry90, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.of_apply]

/-- `Ry90` has determinant one. -/
lemma Ry90_det : Ry90.det = 1 := by
  simp [Ry90, Matrix.det_fin_three]

/-- `Ry90` has order four. -/
lemma Ry90_order :
    Ry90 ^ 4 = 1 ∧ ∀ m : ℕ, 0 < m → m < 4 → Ry90 ^ m ≠ 1 := by
  have h2v : Ry90 ^ 2 = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ry90, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.of_apply]
  have h3v : Ry90 ^ 3 = !![0, 0, -1; 0, 1, 0; 1, 0, 0] := by
    have e3 : Ry90 ^ 3 = Ry90 ^ 2 * Ry90 := pow_succ Ry90 2
    rw [e3, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ry90, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  have h4 : Ry90 ^ 4 = 1 := by
    have e4 : Ry90 ^ 4 = (Ry90 ^ 2) ^ 2 := pow_mul Ry90 2 2
    rw [e4, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  refine ⟨h4, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    norm_num [pow_one, Ry90, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    norm_num [h2v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) h
    norm_num [h3v, Matrix.of_apply] at e

/-- `Ry90` has trace one. -/
lemma Ry90_trace : Ry90.trace = 1 := by
  simp [Ry90, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three,
    Matrix.of_apply]

/-- `Rz90` is orthogonal. -/
lemma Rz90_orthogonal : Rz90ᵀ * Rz90 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz90, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.of_apply]

/-- `Rz90` has determinant one. -/
lemma Rz90_det : Rz90.det = 1 := by
  simp [Rz90, Matrix.det_fin_three]

/-- `Rz90` has order four. -/
lemma Rz90_order :
    Rz90 ^ 4 = 1 ∧ ∀ m : ℕ, 0 < m → m < 4 → Rz90 ^ m ≠ 1 := by
  have h2v : Rz90 ^ 2 = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rz90, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.of_apply]
  have h3v : Rz90 ^ 3 = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
    have e3 : Rz90 ^ 3 = Rz90 ^ 2 * Rz90 := pow_succ Rz90 2
    rw [e3, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rz90, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  have h4 : Rz90 ^ 4 = 1 := by
    have e4 : Rz90 ^ 4 = (Rz90 ^ 2) ^ 2 := pow_mul Rz90 2 2
    rw [e4, h2v]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply]
  refine ⟨h4, ?_⟩
  intro m hmpos hmlt
  interval_cases m
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    norm_num [pow_one, Rz90, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    norm_num [h2v, Matrix.of_apply] at e
  · intro h
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
    norm_num [h3v, Matrix.of_apply] at e

/-- `Rz90` has trace one. -/
lemma Rz90_trace : Rz90.trace = 1 := by
  simp [Rz90, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three,
    Matrix.of_apply]

/-- A signed permutation matrix: each row has exactly one nonzero entry, `±1`,
at column `σ i`. The cubic point group (reference data: the 24 rotations) is
the set of signed permutation matrices with determinant one. -/
def IsSignedPerm (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ s : Fin 3 → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ i j, M i j = if σ i = j then s i else 0

/-- `Rx90` is a signed permutation matrix. -/
lemma Rx90_signed : IsSignedPerm Rx90 := by
  refine ⟨Equiv.swap 1 2, ![1, -1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

/-- `Ry90` is a signed permutation matrix. -/
lemma Ry90_signed : IsSignedPerm Ry90 := by
  refine ⟨Equiv.swap 0 2, ![1, 1, -1], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

/-- `Rz90` is a signed permutation matrix. -/
lemma Rz90_signed : IsSignedPerm Rz90 := by
  refine ⟨Equiv.swap 0 1, ![-1, 1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

/-- Signed permutation matrices are closed under multiplication. -/
lemma signedPerm_mul (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : IsSignedPerm M) (hN : IsSignedPerm N) :
    IsSignedPerm (M * N) := by
  obtain ⟨σ, s, hs, hM⟩ := hM
  obtain ⟨τ, t, ht, hN⟩ := hN
  refine ⟨σ.trans τ, fun i => s i * t (σ i), ?_, ?_⟩
  · intro i
    rcases hs i with h1 | h1 <;> rcases ht (σ i) with h2 | h2 <;>
      simp [h1, h2]
  · intro i j
    rw [Matrix.mul_apply]
    by_cases hj : (σ.trans τ) i = j
    · have htj : τ (σ i) = j := by rwa [Equiv.trans_apply] at hj
      have hsum : ∑ k, M i k * N k j = M i (σ i) * N (σ i) j := by
        refine Finset.sum_eq_single_of_mem (σ i) (Finset.mem_univ _) ?_
        intro k _ hk
        have hMik : M i k = 0 := by rw [hM i k, ite_eq_right (Ne.symm hk)]
        rw [hMik, zero_mul]
      rw [ite_eq_left hj, hsum, hM i (σ i), hN (σ i) j, ite_eq_left rfl, ite_eq_left htj]
    · rw [ite_eq_right hj]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k = σ i
      · subst hk
        have htj : τ (σ i) ≠ j := by rwa [Equiv.trans_apply] at hj
        have hNk : N (σ i) j = 0 := by rw [hN (σ i) j, ite_eq_right htj]
        rw [hNk, mul_zero]
      · have hMik : M i k = 0 := by
          rw [hM i k, ite_eq_right (fun h => hk h.symm)]
        rw [hMik, zero_mul]

/-! ## E. Neumann: inversion and cubic invariance -/

/-- Inversion kills polar vectors: `v = -v` forces `v = 0`. -/
lemma polarVector_inversion (v : Fin 3 → ℝ) (h : v = -v) : v = 0 := by
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
  linarith

/-- Inversion kills rank-3 polar tensors. -/
lemma polarRank3_inversion (T : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (h : ∀ i j k, T i j k = -T i j k) : T = 0 := by
  funext i j k
  have hijk := h i j k
  simp only [Pi.zero_apply] at hijk ⊢
  linarith

/-- Cubic invariance forces a symmetric rank-2 tensor to be scalar: if `S` is
symmetric and invariant under conjugation by the three cubic generators, then
`S = s • 1` with `s = S 0 0`. -/
lemma symmetric_cubic_is_scalar (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymm : Sᵀ = S)
    (hx : Rx90ᵀ * S * Rx90 = S)
    (hy : Ry90ᵀ * S * Ry90 = S)
    (hz : Rz90ᵀ * S * Rz90 = S) :
    S = (S 0 0) • 1 := by
  have s10 : S 1 0 = S 0 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) hsymm
    simpa [Matrix.transpose_apply] using h
  have s20 : S 2 0 = S 0 2 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) hsymm
    simpa [Matrix.transpose_apply] using h
  have s21 : S 2 1 = S 1 2 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hsymm
    simpa [Matrix.transpose_apply] using h
  have hz00 : S 1 1 = S 0 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hz
    simp [Rz90, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] at h
    linear_combination h
  have hy00 : S 2 2 = S 0 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hy
    simp [Ry90, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] at h
    linear_combination h
  have o01 : S 0 1 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) hz
    simp [Rz90, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] at h
    linarith [h, s10]
  have o02 : S 0 2 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) hy
    simp [Ry90, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] at h
    linarith [h, s20]
  have o12 : S 1 2 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hx
    simp [Rx90, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] at h
    linarith [h, s21]
  refine Matrix.ext ?_
  simp only [split3]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp [Matrix.smul_apply] <;>
    linarith [hz00, hy00, o01, o02, o12, s10, s20, s21]

/-! ## F. Independent elastic constants -/

/-- The upper triangle of `6 × 6` indices. -/
def upperTri : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun p => p.1 ≤ p.2)

/-- The upper triangle of `6 × 6` Voigt indices has 21 positions. With
`eq_of_agree_on_upperTri` and `exists_symm_of_upperTri`, a triclinic
(unconstrained symmetric) Voigt matrix has 21 independent elastic constants. -/
lemma upperTri_card : upperTri.card = 21 := by
  decide

/-- A symmetric `6 × 6` matrix is determined by its upper triangle. -/
lemma eq_of_agree_on_upperTri (A B : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hag : ∀ p ∈ upperTri, A p.1 p.2 = B p.1 p.2) : A = B := by
  refine Matrix.ext ?_
  intro i j
  by_cases hij : i ≤ j
  · exact hag (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
  · have hji : j ≤ i := le_of_lt (not_le.mp hij)
    have e := hag (j, i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩)
    have hAij : A i j = A j i := by
      have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M j i) hA
      simpa [Matrix.transpose_apply] using h
    have hBij : B i j = B j i := by
      have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M j i) hB
      simpa [Matrix.transpose_apply] using h
    linear_combination e + hAij - hBij

/-- Every assignment of values to the 21 upper-triangle positions comes from a
symmetric `6 × 6` matrix, so the upper-triangle entries are independent. -/
lemma exists_symm_of_upperTri (f : Fin 6 × Fin 6 → ℝ) :
    ∃ A : Matrix (Fin 6) (Fin 6) ℝ, Aᵀ = A ∧ ∀ p ∈ upperTri, A p.1 p.2 = f p := by
  refine ⟨Matrix.of fun i j => if i ≤ j then f (i, j) else f (j, i), ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h.le, not_le.mpr h]
    · simp
    · simp [h.le, not_le.mpr h]
  · rintro ⟨i, j⟩ hp
    have hij : i ≤ j := (Finset.mem_filter.mp hp).2
    simp [hij]

/-- Voigt index permutation for swapping axes `x ↔ y`. -/
def voigtSwap01 : Fin 6 → Fin 6 := ![1, 0, 2, 4, 3, 5]

/-- Voigt index permutation for swapping axes `x ↔ z`. -/
def voigtSwap02 : Fin 6 → Fin 6 := ![2, 1, 0, 5, 4, 3]

/-- Voigt index permutation for swapping axes `y ↔ z`. -/
def voigtSwap12 : Fin 6 → Fin 6 := ![0, 2, 1, 3, 5, 4]

/-- Voigt index permutation for the `z`-axis quarter-turn `Rz90ᵀ = Rz90⁻¹` (rotation by `-90°`),
the action computed by `voigtRotate` (`voigtRotate_Rz90_transpose_apply`). -/
def voigtRotZ90 : Fin 6 → Fin 6 := ![1, 0, 2, 4, 3, 5]

/-- Voigt signs for the `z`-axis quarter-turn `Rz90ᵀ = Rz90⁻¹` (rotation by `-90°`), the action
computed by `voigtRotate` (`voigtRotate_Rz90_transpose_apply`). -/
def voigtRotZ90Sign : Fin 6 → ℝ := ![1, 1, 1, -1, 1, -1]

/-- The cubic Voigt family: `3 × 3` normal block with `c11` on the diagonal
and `c12` off-diagonal, `3 × 3` shear block `c44 • 1`, zero couplings:
```
c11 c12 c12 0   0   0
c12 c11 c12 0   0   0
c12 c12 c11 0   0   0
0   0   0   c44 0   0
0   0   0   0   c44 0
0   0   0   0   0   c44
``` -/
def cubicVoigt (c11 c12 c44 : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![c11, c12, c12, 0, 0, 0;
     c12, c11, c12, 0, 0, 0;
     c12, c12, c11, 0, 0, 0;
     0, 0, 0, c44, 0, 0;
     0, 0, 0, 0, c44, 0;
     0, 0, 0, 0, 0, c44]

/-- A symmetric Voigt matrix invariant under axis permutations and the
`z`-axis quarter-turn is cubic. The invariances are stated as explicit entry
equations; `hrot` is the entry form of `voigtRotate Rz90ᵀ C = C`
(`voigtRotate_Rz90_transpose_apply`). Note: axis permutations alone do NOT imply the cubic form (the
test file exhibits a permutation-invariant counterexample with nonzero
normal-shear couplings), so the quarter-turn invariance, with its signs, is
an essential hypothesis. -/
lemma eq_cubicVoigt_of_voigtInvariance (C : Matrix (Fin 6) (Fin 6) ℝ)
    (hsymm : Cᵀ = C)
    (h01 : ∀ i j, C i j = C (voigtSwap01 i) (voigtSwap01 j))
    (h02 : ∀ i j, C i j = C (voigtSwap02 i) (voigtSwap02 j))
    (h12 : ∀ i j, C i j = C (voigtSwap12 i) (voigtSwap12 j))
    (hrot : ∀ i j, C i j =
      voigtRotZ90Sign i * voigtRotZ90Sign j * C (voigtRotZ90 i) (voigtRotZ90 j)) :
    C = cubicVoigt (C 0 0) (C 0 1) (C 3 3) := by
  have symm : ∀ i j, C i j = C j i := fun i j => by
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M j i) hsymm
    simpa [Matrix.transpose_apply] using h
  have e11 : C 1 1 = C 0 0 := h01 1 1
  have e10 : C 1 0 = C 0 1 := h01 1 0
  have e02_12 : C 0 2 = C 1 2 := h01 0 2
  have e21_20 : C 2 1 = C 2 0 := h01 2 1
  have e44 : C 4 4 = C 3 3 := h01 4 4
  have p03_14 : C 0 3 = C 1 4 := h01 0 3
  have p04_13 : C 0 4 = C 1 3 := h01 0 4
  have p05_15 : C 0 5 = C 1 5 := h01 0 5
  have e22 : C 2 2 = C 0 0 := h02 2 2
  have e01_21 : C 0 1 = C 2 1 := h02 0 1
  have e55 : C 5 5 = C 3 3 := h02 5 5
  have p03_25 : C 0 3 = C 2 5 := h02 0 3
  have p04_24 : C 0 4 = C 2 4 := h02 0 4
  have p05_23 : C 0 5 = C 2 3 := h02 0 5
  have p04_05 : C 0 4 = C 0 5 := h12 0 4
  have r03 : C 0 3 = -C 1 4 := by
    have h := hrot 0 3
    rw [show voigtRotZ90Sign 0 = 1 from rfl,
      show voigtRotZ90Sign 3 = -1 from rfl,
      show voigtRotZ90 0 = 1 from rfl,
      show voigtRotZ90 3 = 4 from rfl] at h
    linear_combination h
  have r04 : C 0 4 = C 1 3 := by
    have h := hrot 0 4
    rw [show voigtRotZ90Sign 0 = 1 from rfl,
      show voigtRotZ90Sign 4 = 1 from rfl,
      show voigtRotZ90 0 = 1 from rfl,
      show voigtRotZ90 4 = 3 from rfl] at h
    linear_combination h
  have r13 : C 1 3 = -C 0 4 := by
    have h := hrot 1 3
    rw [show voigtRotZ90Sign 1 = 1 from rfl,
      show voigtRotZ90Sign 3 = -1 from rfl,
      show voigtRotZ90 1 = 0 from rfl,
      show voigtRotZ90 3 = 4 from rfl] at h
    linear_combination h
  have r15 : C 1 5 = -C 0 5 := by
    have h := hrot 1 5
    rw [show voigtRotZ90Sign 1 = 1 from rfl,
      show voigtRotZ90Sign 5 = -1 from rfl,
      show voigtRotZ90 1 = 0 from rfl,
      show voigtRotZ90 5 = 5 from rfl] at h
    linear_combination h
  have r34 : C 3 4 = -C 4 3 := by
    have h := hrot 3 4
    rw [show voigtRotZ90Sign 3 = -1 from rfl,
      show voigtRotZ90Sign 4 = 1 from rfl,
      show voigtRotZ90 3 = 4 from rfl,
      show voigtRotZ90 4 = 3 from rfl] at h
    linear_combination h
  have r35 : C 3 5 = C 4 5 := by
    have h := hrot 3 5
    rw [show voigtRotZ90Sign 3 = -1 from rfl,
      show voigtRotZ90Sign 5 = -1 from rfl,
      show voigtRotZ90 3 = 4 from rfl,
      show voigtRotZ90 5 = 5 from rfl] at h
    linear_combination h
  have r45 : C 4 5 = -C 3 5 := by
    have h := hrot 4 5
    rw [show voigtRotZ90Sign 4 = 1 from rfl,
      show voigtRotZ90Sign 5 = -1 from rfl,
      show voigtRotZ90 4 = 3 from rfl,
      show voigtRotZ90 5 = 5 from rfl] at h
    linear_combination h
  have s03 : C 0 3 = C 3 0 := symm 0 3
  have s04 : C 0 4 = C 4 0 := symm 0 4
  have s05 : C 0 5 = C 5 0 := symm 0 5
  have s12 : C 1 2 = C 2 1 := symm 1 2
  have s13 : C 1 3 = C 3 1 := symm 1 3
  have s14 : C 1 4 = C 4 1 := symm 1 4
  have s15 : C 1 5 = C 5 1 := symm 1 5
  have s23 : C 2 3 = C 3 2 := symm 2 3
  have s24 : C 2 4 = C 4 2 := symm 2 4
  have s25 : C 2 5 = C 5 2 := symm 2 5
  have s34 : C 3 4 = C 4 3 := symm 3 4
  have s35 : C 3 5 = C 5 3 := symm 3 5
  have s45 : C 4 5 = C 5 4 := symm 4 5
  have z03 : C 0 3 = 0 := by linarith [p03_14, r03]
  have z04 : C 0 4 = 0 := by linarith [r04, r13]
  have z05 : C 0 5 = 0 := by linarith [p04_05, z04]
  have z13 : C 1 3 = 0 := by linarith [p04_13, z04]
  have z14 : C 1 4 = 0 := by linarith [p03_14, z03]
  have z15 : C 1 5 = 0 := by linarith [p05_15, z05]
  have z23 : C 2 3 = 0 := by linarith [p05_23, z05]
  have z24 : C 2 4 = 0 := by linarith [p04_24, z04]
  have z25 : C 2 5 = 0 := by linarith [p03_25, z03]
  have z34 : C 3 4 = 0 := by linarith [r34, s34]
  have z35 : C 3 5 = 0 := by linarith [r35, r45]
  have z45 : C 4 5 = 0 := by linarith [r35, r45]
  have e21 : C 2 1 = C 0 1 := by linarith [e01_21]
  have e20 : C 2 0 = C 0 1 := by linarith [e21_20, e21]
  have e12 : C 1 2 = C 0 1 := by linarith [e21, s12]
  have e02 : C 0 2 = C 0 1 := by linarith [e02_12, e12]
  refine Matrix.ext ?_
  simp only [split6]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [cubicVoigt, Matrix.of_apply] <;>
    linarith [e11, e10, e02, e20, e12, e21, e22, e44, e55,
      z03, z04, z05, z13, z14, z15, z23, z24, z25, z34, z35, z45,
      s03, s04, s05, s13, s14, s15, s23, s24, s25, s34, s35, s45]

/-- The cubic family is invariant under the `x ↔ y` axis swap. -/
lemma cubicVoigt_swap01 (c11 c12 c44 : ℝ) (i j : Fin 6) :
    cubicVoigt c11 c12 c44 i j
      = cubicVoigt c11 c12 c44 (voigtSwap01 i) (voigtSwap01 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [cubicVoigt, Matrix.of_apply, voigtSwap01]

/-- The cubic family is invariant under the `x ↔ z` axis swap. -/
lemma cubicVoigt_swap02 (c11 c12 c44 : ℝ) (i j : Fin 6) :
    cubicVoigt c11 c12 c44 i j
      = cubicVoigt c11 c12 c44 (voigtSwap02 i) (voigtSwap02 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [cubicVoigt, Matrix.of_apply, voigtSwap02]

/-- The cubic family is invariant under the `y ↔ z` axis swap. -/
lemma cubicVoigt_swap12 (c11 c12 c44 : ℝ) (i j : Fin 6) :
    cubicVoigt c11 c12 c44 i j
      = cubicVoigt c11 c12 c44 (voigtSwap12 i) (voigtSwap12 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [cubicVoigt, Matrix.of_apply, voigtSwap12]

/-- The cubic family is invariant under the `z`-axis quarter-turn `Rz90ᵀ`, in entry form. -/
lemma cubicVoigt_rotZ90 (c11 c12 c44 : ℝ) (i j : Fin 6) :
    cubicVoigt c11 c12 c44 i j = voigtRotZ90Sign i * voigtRotZ90Sign j *
      cubicVoigt c11 c12 c44 (voigtRotZ90 i) (voigtRotZ90 j) := by
  fin_cases i <;> fin_cases j <;>
    simp [cubicVoigt, Matrix.of_apply, voigtRotZ90, voigtRotZ90Sign]

/-- The cubic family consists of symmetric matrices. -/
lemma cubicVoigt_transpose (c11 c12 c44 : ℝ) :
    (cubicVoigt c11 c12 c44)ᵀ = cubicVoigt c11 c12 c44 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicVoigt]

/-- The three cubic constants are independent: the family is injective in
`(c11, c12, c44)`. -/
lemma cubicVoigt_inj {c11 c12 c44 d11 d12 d44 : ℝ}
    (h : cubicVoigt c11 c12 c44 = cubicVoigt d11 d12 d44) :
    c11 = d11 ∧ c12 = d12 ∧ c44 = d44 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cubicVoigt] using congrFun (congrFun h 0) 0
  · simpa [cubicVoigt] using congrFun (congrFun h 0) 1
  · simpa [cubicVoigt] using congrFun (congrFun h 3) 3

/-- The isotropic (Lamé) Voigt family. -/
def isotropicVoigt (lam mu : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  cubicVoigt (lam + 2 * mu) lam mu

/-- `isotropicVoigt` is a cubic-family matrix. -/
lemma isotropicVoigt_isCubic (lam mu : ℝ) :
    isotropicVoigt lam mu = cubicVoigt (lam + 2 * mu) lam mu := rfl

/-- The isotropic family satisfies the extra relation
`(c11 - c12) = 2 * c44`. Conversely, `relation_of_voigtRotate_Rz45` derives
this relation for a cubic matrix from invariance under the `45°` rotation about
`z`. -/
lemma isotropicVoigt_relation (lam mu : ℝ) :
    isotropicVoigt lam mu 0 0 - isotropicVoigt lam mu 0 1
      = 2 * isotropicVoigt lam mu 3 3 := by
  have e11 : isotropicVoigt lam mu 0 0 = lam + 2 * mu := by
    simp [isotropicVoigt, cubicVoigt, Matrix.of_apply]
  have e12 : isotropicVoigt lam mu 0 1 = lam := by
    simp [isotropicVoigt, cubicVoigt, Matrix.of_apply]
  have e44 : isotropicVoigt lam mu 3 3 = mu := by
    simp [isotropicVoigt, cubicVoigt, Matrix.of_apply]
  rw [e11, e12, e44]
  ring

/-- Converse: a cubic-family matrix satisfying `(c11 - c12) = 2 * c44` lies in
the Lamé family. -/
lemma eq_isotropicVoigt_of_relation (c11 c12 c44 : ℝ)
    (h : c11 - c12 = 2 * c44) :
    cubicVoigt c11 c12 c44 = isotropicVoigt c12 c44 := by
  have e : c11 = c12 + 2 * c44 := by linarith
  rw [e]
  rfl

/-- The isotropic family is invariant under the `x ↔ y` axis swap. -/
lemma isotropicVoigt_swap01 (lam mu : ℝ) (i j : Fin 6) :
    isotropicVoigt lam mu i j
      = isotropicVoigt lam mu (voigtSwap01 i) (voigtSwap01 j) := by
  rw [isotropicVoigt_isCubic]
  exact cubicVoigt_swap01 _ _ _ i j

/-- The isotropic family is invariant under the `x ↔ z` axis swap. -/
lemma isotropicVoigt_swap02 (lam mu : ℝ) (i j : Fin 6) :
    isotropicVoigt lam mu i j
      = isotropicVoigt lam mu (voigtSwap02 i) (voigtSwap02 j) := by
  rw [isotropicVoigt_isCubic]
  exact cubicVoigt_swap02 _ _ _ i j

/-- The isotropic family is invariant under the `y ↔ z` axis swap. -/
lemma isotropicVoigt_swap12 (lam mu : ℝ) (i j : Fin 6) :
    isotropicVoigt lam mu i j
      = isotropicVoigt lam mu (voigtSwap12 i) (voigtSwap12 j) := by
  rw [isotropicVoigt_isCubic]
  exact cubicVoigt_swap12 _ _ _ i j

/-- The isotropic family is invariant under the `z`-axis quarter-turn `Rz90ᵀ`, in entry form. -/
lemma isotropicVoigt_rotZ90 (lam mu : ℝ) (i j : Fin 6) :
    isotropicVoigt lam mu i j = voigtRotZ90Sign i * voigtRotZ90Sign j *
      isotropicVoigt lam mu (voigtRotZ90 i) (voigtRotZ90 j) := by
  rw [isotropicVoigt_isCubic]
  exact cubicVoigt_rotZ90 _ _ _ i j

/-- The two Lamé constants are independent: the family is injective in
`(lam, mu)`. -/
lemma isotropicVoigt_inj {lam mu lam' mu' : ℝ}
    (h : isotropicVoigt lam mu = isotropicVoigt lam' mu') : lam = lam' ∧ mu = mu' := by
  rw [isotropicVoigt_isCubic, isotropicVoigt_isCubic] at h
  obtain ⟨-, h12, h44⟩ := cubicVoigt_inj h
  exact ⟨h12, h44⟩

/-! ### The action of a `3 × 3` matrix on Voigt matrices -/

/-- The Voigt index of the symmetric index pair `(i, j)`:
`xx ↦ 0`, `yy ↦ 1`, `zz ↦ 2`, `yz ↦ 3`, `xz ↦ 4`, `xy ↦ 5`. -/
def voigtIndex : Fin 3 → Fin 3 → Fin 6 := ![![0, 5, 4], ![5, 1, 3], ![4, 3, 2]]

/-- The first index of the pair encoded by a Voigt index. -/
def voigtFst : Fin 6 → Fin 3 := ![0, 1, 2, 1, 0, 0]

/-- The second index of the pair encoded by a Voigt index. -/
def voigtSnd : Fin 6 → Fin 3 := ![0, 1, 2, 2, 2, 1]

/-- Encoding the pair of a Voigt index gives the index back. -/
lemma voigtIndex_fst_snd (I : Fin 6) : voigtIndex (voigtFst I) (voigtSnd I) = I := by
  fin_cases I <;> rfl

/-- The action of a `3 × 3` matrix `R` on a Voigt stiffness matrix `C`. The
matrix `C` encodes the rank-four elasticity tensor
`c i j k l = C (voigtIndex i j) (voigtIndex k l)`, and the action is the tensor
transformation `c' i j k l = ∑ R i a * R j b * R k c * R l d * c a b c d`,
read back in Voigt form. Neumann invariance of a stiffness matrix `C` under a
point-group element `R` is the equation `voigtRotate R C = C`. -/
def voigtRotate (R : Matrix (Fin 3) (Fin 3) ℝ) (C : Matrix (Fin 6) (Fin 6) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun I J => ∑ a, ∑ b, ∑ c, ∑ d,
    R (voigtFst I) a * R (voigtSnd I) b * R (voigtFst J) c * R (voigtSnd J) d *
      C (voigtIndex a b) (voigtIndex c d)

/-- The identity matrix acts trivially. -/
lemma voigtRotate_one (C : Matrix (Fin 6) (Fin 6) ℝ) : voigtRotate 1 C = C := by
  ext I J
  simp only [voigtRotate, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [voigtIndex_fst_snd, voigtIndex_fst_snd]

set_option maxHeartbeats 1000000 in -- 36 entries, each a sum of 81 terms
/-- The entry equations of `voigtRotZ90` and `voigtRotZ90Sign` are the action of the quarter-turn
`Rz90ᵀ = Rz90⁻¹`, the rotation by `-90°` about `z`. -/
theorem voigtRotate_Rz90_transpose_apply (C : Matrix (Fin 6) (Fin 6) ℝ) (I J : Fin 6) :
    voigtRotate Rz90ᵀ C I J =
      voigtRotZ90Sign I * voigtRotZ90Sign J * C (voigtRotZ90 I) (voigtRotZ90 J) := by
  fin_cases I <;> fin_cases J <;>
    simp [voigtRotate, Rz90, voigtFst, voigtSnd, voigtIndex, voigtRotZ90, voigtRotZ90Sign,
      Fin.sum_univ_three]

/-- The rotation by `45°` about the `z`-axis. -/
noncomputable def Rz45 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![√2 / 2, -(√2 / 2), 0; √2 / 2, √2 / 2, 0; 0, 0, 1]

/-- `cos² 45° = 1 / 2`. -/
private lemma sqrt_two_half_mul_self : √2 / 2 * (√2 / 2) = (1 / 2 : ℝ) := by
  have h : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  linear_combination h / 4

/-- `Rz45` is orthogonal. -/
lemma Rz45_orthogonal : Rz45ᵀ * Rz45 = 1 := by
  have h := sqrt_two_half_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz45, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    linarith [h]

/-- `Rz45` has determinant one. -/
lemma Rz45_det : Rz45.det = 1 := by
  have h := sqrt_two_half_mul_self
  simp [Rz45, Matrix.det_fin_three]
  linarith [h]

/-- `Rz45` squares to the quarter-turn `Rz90`. -/
lemma Rz45_sq : Rz45 ^ 2 = Rz90 := by
  have h := sqrt_two_half_mul_self
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz45, Rz90, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linarith [h]

/-- The `xy` shear entry of a cubic matrix rotated by `45°` about `z` is
`(c11 - c12) / 2`. -/
lemma voigtRotate_Rz45_cubicVoigt_55 (c11 c12 c44 : ℝ) :
    voigtRotate Rz45 (cubicVoigt c11 c12 c44) 5 5 = (c11 - c12) / 2 := by
  have h := sqrt_two_half_mul_self
  simp [voigtRotate, Rz45, cubicVoigt, voigtFst, voigtSnd, voigtIndex, Fin.sum_univ_three]
  ring_nf
  linear_combination (c11 - c12) / 2 * (√2 ^ 2 + 2) * h

/-- Invariance of a cubic matrix under the `45°` rotation about `z` forces the
isotropy relation `c11 - c12 = 2 * c44`. -/
theorem relation_of_voigtRotate_Rz45 (c11 c12 c44 : ℝ)
    (h : voigtRotate Rz45 (cubicVoigt c11 c12 c44) = cubicVoigt c11 c12 c44) :
    c11 - c12 = 2 * c44 := by
  have e := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 5 5) h
  have e55 : cubicVoigt c11 c12 c44 5 5 = c44 := by simp [cubicVoigt]
  simp only [voigtRotate_Rz45_cubicVoigt_55, e55] at e
  linarith

/-- A symmetric Voigt matrix invariant under the axis swaps and the `z`
quarter-turn (as in `eq_cubicVoigt_of_voigtInvariance`) and under the `45°`
rotation about `z` lies in the 2-parameter Lamé family. -/
theorem eq_isotropicVoigt_of_rotationInvariance (C : Matrix (Fin 6) (Fin 6) ℝ)
    (hsymm : Cᵀ = C)
    (h01 : ∀ i j, C i j = C (voigtSwap01 i) (voigtSwap01 j))
    (h02 : ∀ i j, C i j = C (voigtSwap02 i) (voigtSwap02 j))
    (h12 : ∀ i j, C i j = C (voigtSwap12 i) (voigtSwap12 j))
    (hrot : ∀ i j, C i j =
      voigtRotZ90Sign i * voigtRotZ90Sign j * C (voigtRotZ90 i) (voigtRotZ90 j))
    (h45 : voigtRotate Rz45 C = C) :
    C = isotropicVoigt (C 0 1) (C 3 3) := by
  have hC := eq_cubicVoigt_of_voigtInvariance C hsymm h01 h02 h12 hrot
  rw [hC] at h45
  calc C = cubicVoigt (C 0 0) (C 0 1) (C 3 3) := hC
    _ = isotropicVoigt (C 0 1) (C 3 3) :=
      eq_isotropicVoigt_of_relation _ _ _ (relation_of_voigtRotate_Rz45 _ _ _ h45)

/-- The Lamé family in tensor form:
`c a b c d = lam * δ a b * δ c d + mu * (δ a c * δ b d + δ a d * δ b c)`. -/
lemma isotropicVoigt_voigtIndex (lam mu : ℝ) (a b c d : Fin 3) :
    isotropicVoigt lam mu (voigtIndex a b) (voigtIndex c d) =
      lam * (1 : Matrix (Fin 3) (Fin 3) ℝ) a b * (1 : Matrix (Fin 3) (Fin 3) ℝ) c d +
      mu * ((1 : Matrix (Fin 3) (Fin 3) ℝ) a c * (1 : Matrix (Fin 3) (Fin 3) ℝ) b d +
        (1 : Matrix (Fin 3) (Fin 3) ℝ) a d * (1 : Matrix (Fin 3) (Fin 3) ℝ) b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [isotropicVoigt, cubicVoigt, voigtIndex] <;> ring

/-- The rotated Lamé tensor, written through the Gram matrix `R * Rᵀ`. -/
private lemma sum_rotate_lame (R : Matrix (Fin 3) (Fin 3) ℝ) (lam mu : ℝ)
    (i j k l : Fin 3) :
    ∑ a, ∑ b, ∑ c, ∑ d, R i a * R j b * R k c * R l d *
      (lam * (1 : Matrix (Fin 3) (Fin 3) ℝ) a b * (1 : Matrix (Fin 3) (Fin 3) ℝ) c d +
        mu * ((1 : Matrix (Fin 3) (Fin 3) ℝ) a c * (1 : Matrix (Fin 3) (Fin 3) ℝ) b d +
          (1 : Matrix (Fin 3) (Fin 3) ℝ) a d * (1 : Matrix (Fin 3) (Fin 3) ℝ) b c)) =
      lam * (R * Rᵀ) i j * (R * Rᵀ) k l +
        mu * ((R * Rᵀ) i k * (R * Rᵀ) j l + (R * Rᵀ) i l * (R * Rᵀ) j k) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.one_apply,
    Fin.reduceEq, ite_true, ite_false]
  ring

/-- The Lamé family is invariant under every orthogonal matrix, so its members
are isotropic. -/
theorem voigtRotate_isotropicVoigt (R : Matrix (Fin 3) (Fin 3) ℝ) (horth : Rᵀ * R = 1)
    (lam mu : ℝ) : voigtRotate R (isotropicVoigt lam mu) = isotropicVoigt lam mu := by
  have hR : R * Rᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ rfl).mp horth
  ext I J
  simp only [voigtRotate, Matrix.of_apply, isotropicVoigt_voigtIndex]
  rw [sum_rotate_lame, hR, ← isotropicVoigt_voigtIndex, voigtIndex_fst_snd,
    voigtIndex_fst_snd]

end Crystallography.Symmetry
