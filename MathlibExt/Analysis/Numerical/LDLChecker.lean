/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Order.Star.Rat

@[expose] public section

/-
Exact rational LDLᵀ certificates for positive semidefinite matrices over `ℚ`.

A certificate for `Q.PosSemidef` is a unit lower-triangular matrix `L` and a
diagonal `d` with all entries nonnegative such that `Q = L * diagonal d * Lᵀ`.
This file defines the certificate predicate `IsUnitLowerTriangular`, proves the
certificate sound (`ldl_posSemidef`), and provides a verified executable
checker (`checkLDL` / `checkLDL_sound`).

The mathematics is the standard Gram-matrix / congruence argument: a diagonal
matrix with nonnegative entries is positive semidefinite, and congruence
`B * A * Bᵀ` preserves positive semidefiniteness. See e.g. Horn and Johnson,
"Matrix Analysis" (Cambridge University Press), Chapter 7, and Golub and
Van Loan, "Matrix Computations" (Johns Hopkins University Press), Chapter 4.
The use of exact rational factorizations as independently checkable
positive-semidefiniteness certificates follows Prajna and Jadbabaie (HSCC 2004).
-/

namespace SOSCertificate.LDL

/-- Unit lower-triangular matrices over `ℚ`, indexed by `Fin m`: ones on the
diagonal and zeros strictly above it. -/
def IsUnitLowerTriangular {m : ℕ} (L : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  L.IsLowerTriangular ∧ ∀ i, L i i = 1

/-- Soundness of exact rational LDLᵀ certificates: a matrix that factors as
`L * diagonal d * Lᵀ` with `L` unit lower-triangular and `d` entrywise
nonnegative is positive semidefinite. The triangularity hypothesis is part of
the certificate notion; positive semidefiniteness itself follows from the
factorization equation alone, since `diagonal d` is positive semidefinite and
congruence preserves positive semidefiniteness. -/
theorem ldl_posSemidef {m : ℕ} (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (_hL : IsUnitLowerTriangular L) (hd : ∀ i, 0 ≤ d i)
    (Q : Matrix (Fin m) (Fin m) ℚ)
    (hQ : Q = L * Matrix.diagonal d * L.transpose) :
    Q.PosSemidef := by
  subst hQ
  have hD : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd
  have hT : L.transpose = L.conjTranspose :=
    (Matrix.conjTranspose_eq_transpose_of_trivial L).symm
  rw [hT]
  exact hD.mul_mul_conjTranspose_same L

/-- Each entry of `L * diagonal d * Lᵀ` is a single sum. -/
theorem ldl_entry {m : ℕ} (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (i j : Fin m) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

instance ldlEntryDecidable {m : ℕ} {Q L : Matrix (Fin m) (Fin m) ℚ}
    {d : Fin m → ℚ} :
    Decidable (∀ i j, Q i j = ∑ k, L i k * d k * L j k) :=
  decidable_of_iff
    (∀ ij : Fin m × Fin m, Q ij.1 ij.2 = ∑ k, L ij.1 k * d k * L ij.2 k)
    ⟨fun h i j => h (i, j), fun h ij => h ij.1 ij.2⟩

/-- Executable checker for exact rational LDLᵀ certificates. It decides the
three certificate conditions: `L` is unit lower-triangular (Mathlib's
`IsLowerTriangular` with ones on the diagonal), `d` is entrywise
nonnegative, and the factorization equation holds entrywise,
`Q i j = ∑ k, L i k * d k * L j k` (a single sum per entry, decidable on
`ℚ` entries). -/
def checkLDL {m : ℕ} (Q L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) : Bool :=
  decide (L.IsLowerTriangular ∧ ∀ i, L i i = 1) &&
    (decide (∀ i, 0 ≤ d i) && decide (∀ i j, Q i j = ∑ k, L i k * d k * L j k))

/-- The executable checker is sound: whenever it accepts, `Q` is positive
semidefinite. -/
theorem checkLDL_sound {m : ℕ} {Q L : Matrix (Fin m) (Fin m) ℚ} {d : Fin m → ℚ}
    (h : checkLDL Q L d = true) : Q.PosSemidef := by
  unfold checkLDL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨htri, hd, hE⟩ := h
  have hL' : L.IsLowerTriangular ∧ ∀ i, L i i = 1 := of_decide_eq_true htri
  have hL : IsUnitLowerTriangular L := hL'
  have h3 : ∀ i, 0 ≤ d i := of_decide_eq_true hd
  have hE' : ∀ i j, Q i j = ∑ k, L i k * d k * L j k := of_decide_eq_true hE
  have hQ : Q = L * Matrix.diagonal d * L.transpose := by
    apply Matrix.ext
    intro i j
    rw [ldl_entry]
    exact hE' i j
  exact ldl_posSemidef L d hL h3 Q hQ


end SOSCertificate.LDL
