/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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
  (∀ i, L i i = 1) ∧ (∀ i j, i < j → L i j = 0)

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

/-- Executable checker for exact rational LDLᵀ certificates. It decides the
three certificate conditions: `L` is unit lower-triangular (ones on the
diagonal; zeros above it, quantified over index pairs), `d` is entrywise
nonnegative, and the factorization equation
`Q = L * diagonal d * Lᵀ` holds (matrix equality over a `Fintype` is
decidable, decided entrywise). -/
def checkLDL {m : ℕ} (Q L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) : Bool :=
  decide (∀ i, L i i = 1) &&
    (decide (∀ ij : Fin m × Fin m, ij.1 < ij.2 → L ij.1 ij.2 = 0) &&
      (decide (∀ i, 0 ≤ d i) && decide (Q = L * Matrix.diagonal d * L.transpose)))

/-- The executable checker is sound: whenever it accepts, `Q` is positive
semidefinite. -/
theorem checkLDL_sound {m : ℕ} {Q L : Matrix (Fin m) (Fin m) ℚ} {d : Fin m → ℚ}
    (h : checkLDL Q L d = true) : Q.PosSemidef := by
  unfold checkLDL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hdiag, hupper, hd, hQ⟩ := h
  have h1 : ∀ i, L i i = 1 := of_decide_eq_true hdiag
  have h2 : ∀ ij : Fin m × Fin m, ij.1 < ij.2 → L ij.1 ij.2 = 0 :=
    of_decide_eq_true hupper
  have h2' : ∀ i j, i < j → L i j = 0 := fun i j hij => h2 (i, j) hij
  have h3 : ∀ i, 0 ≤ d i := of_decide_eq_true hd
  have h4 : Q = L * Matrix.diagonal d * L.transpose := of_decide_eq_true hQ
  exact ldl_posSemidef L d ⟨h1, h2'⟩ h3 Q h4

#print axioms ldl_posSemidef
#print axioms checkLDL_sound

end SOSCertificate.LDL
