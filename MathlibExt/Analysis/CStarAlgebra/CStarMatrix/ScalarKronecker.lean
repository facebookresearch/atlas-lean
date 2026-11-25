/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Scalar-coordinate Kronecker matrices in the C-star matrix type copy

These are finite scalar actions, not completed tensor products.
The coefficient multiplication need not be commutative. The flattened
constructor uses the existing linear finite-product reindex, with no
replacement of a matrix norm or order.
-/

@[expose] public section

namespace CStarMatrix

noncomputable section

universe u

variable {R : Type u} {l m n l' m' n' : Type*}

/-- Let `R` be a complex module. Let `l` be an index type. Let `m` be an index type. Let `l'` be an
index type. Let `m'` be an index type. For `S : CStarMatrix l m ℂ` and `M : CStarMatrix l' m' R`.
Finite scalar-coordinate Kronecker multiplication, in the C-star `CStarMatrix` representation.
-/
def scalarKronecker [AddCommMonoid R] [Module ℂ R]
    (S : CStarMatrix l m ℂ) (M : CStarMatrix l' m' R) :
    CStarMatrix (l × l') (m × m') R :=
  ofMatrix (Matrix.kroneckerMapBilinear (LinearMap.lsmul ℂ R)
    (ofMatrix.symm S) (ofMatrix.symm M))

/-- Let `R` be a complex module. Let `l` be an index type. Let `m` be an index type. Let `l'` be an
index type. Let `m'` be an index type. For `S : CStarMatrix l m ℂ`, `M : CStarMatrix l' m' R`, `i :
l × l'` and `j : m × m'`. Literal scalar-coordinate entries.
-/
@[simp]
theorem scalarKronecker_apply [AddCommMonoid R] [Module ℂ R]
    (S : CStarMatrix l m ℂ) (M : CStarMatrix l' m' R)
    (i : l × l') (j : m × m') :
    scalarKronecker S M i j = S i.1 j.1 • M i.2 j.2 :=
  rfl

/-- Let `R` be a possibly nonunital, nonassociative semiring. Let `l` be an index type. Let `m` be a
finite index type. Let `n` be an index type. Let `l'` be an index type. Let `m'` be a finite index
type. Let `n'` be an index type. `R` has a complex module structure. The `ℂ`-scalar action on `R` is
compatible with multiplication on both sides. For `S : CStarMatrix l m ℂ`, `T : CStarMatrix m n ℂ`,
`M : CStarMatrix l' m' R` and `N : CStarMatrix m' n' R`. Scalar-coordinate Kronecker multiplication
preserves matrix products without commutative coefficient-ring hypotheses.
-/
theorem scalarKronecker_mul
    [NonUnitalNonAssocSemiring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    [Fintype m] [Fintype m']
    (S : CStarMatrix l m ℂ) (T : CStarMatrix m n ℂ)
    (M : CStarMatrix l' m' R) (N : CStarMatrix m' n' R) :
    scalarKronecker (S * T) (M * N) =
      scalarKronecker S M * scalarKronecker T N := by
  have hcomm : ∀ a b : ℂ, ∀ x y : R,
      (LinearMap.lsmul ℂ R) (a * b) (x * y) =
        (LinearMap.lsmul ℂ R) a x * (LinearMap.lsmul ℂ R) b y := by
    intro a b x y
    simp only [LinearMap.lsmul_apply, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm a b]
  have h := Matrix.kroneckerMapBilinear_mul_mul
    (LinearMap.lsmul ℂ R) hcomm
    (ofMatrix.symm S) (ofMatrix.symm T)
    (ofMatrix.symm M) (ofMatrix.symm N)
  simp only [scalarKronecker, ofMatrix_symm_mul, of_mul_of]
  exact congrArg ofMatrix h

/-- Let `R` be a complex module and let `m`, `n` be natural numbers. For a complex `m × m` matrix `S`
and an `R`-valued `n × n` matrix `M`, scalar-coordinate Kronecker multiplication followed by the
finite-product reindex gives an `R`-valued `m*n × m*n` CStarMatrix.
-/
def scalarKroneckerFin [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ}
    (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R) :
    CStarMatrix (Fin (m * n)) (Fin (m * n)) R :=
  reindexₗ ℂ R finProdFinEquiv finProdFinEquiv (scalarKronecker S M)

/-- Let `R` be a complex module. For natural numbers `m` and `n`, `S : CStarMatrix (Fin m) (Fin m) ℂ`,
`M : CStarMatrix (Fin n) (Fin n) R` and `i` and `j : Fin (m * n)`. The flattened matrix has the
finite-product coordinates.
-/
@[simp]
theorem scalarKroneckerFin_apply [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ}
    (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R)
    (i j : Fin (m * n)) :
    scalarKroneckerFin S M i j =
      S (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 •
        M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  rw [scalarKroneckerFin, reindexₗ_apply_entry, scalarKronecker_apply]

/-- Let `R` be a complex module. For natural numbers `m` and `n` and `S : CStarMatrix (Fin m) (Fin m)
ℂ`. Zero in the coefficient-matrix slot gives zero, including empty indices.
-/
@[simp]
theorem scalarKroneckerFin_zero_right [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ} (S : CStarMatrix (Fin m) (Fin m) ℂ) :
    scalarKroneckerFin S (0 : CStarMatrix (Fin n) (Fin n) R) = 0 := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.zero_apply, smul_zero]

/-- Let `R` be a complex module. For natural numbers `m` and `n` and `M : CStarMatrix (Fin n) (Fin n)
R`. Zero in the scalar-matrix slot gives zero.
-/
@[simp]
theorem scalarKroneckerFin_zero_left [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ} (M : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin (0 : CStarMatrix (Fin m) (Fin m) ℂ) M = 0 := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.zero_apply, zero_smul]

/-- Let `R` be a complex module. For natural numbers `m` and `n`, `S : CStarMatrix (Fin m) (Fin m) ℂ`
and `M` and `N : CStarMatrix (Fin n) (Fin n) R`. Addition in the coefficient-matrix slot.
-/
theorem scalarKroneckerFin_add_right [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ} (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M N : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin S (M + N) =
      scalarKroneckerFin S M + scalarKroneckerFin S N := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.add_apply, smul_add]

/-- Let `R` be a complex module. For natural numbers `m` and `n`, `S` and `T : CStarMatrix (Fin m) (Fin
m) ℂ` and `M : CStarMatrix (Fin n) (Fin n) R`. Addition in the scalar-matrix slot.
-/
theorem scalarKroneckerFin_add_left [AddCommMonoid R] [Module ℂ R]
    {m n : ℕ} (S T : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin (S + T) M =
      scalarKroneckerFin S M + scalarKroneckerFin T M := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.add_apply, add_smul]

/-- Let `R` be a complex module. For natural numbers `m` and `n`, `S : CStarMatrix (Fin m) (Fin m) ℂ`
and `M` and `N : CStarMatrix (Fin n) (Fin n) R`. Subtraction in the coefficient-matrix slot.
-/
theorem scalarKroneckerFin_sub_right [AddCommGroup R] [Module ℂ R]
    {m n : ℕ} (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M N : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin S (M - N) =
      scalarKroneckerFin S M - scalarKroneckerFin S N := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.sub_apply, smul_sub]

/-- Let `R` be a complex module. For natural numbers `m` and `n`, `S` and `T : CStarMatrix (Fin m) (Fin
m) ℂ` and `M : CStarMatrix (Fin n) (Fin n) R`. Subtraction in the scalar-matrix slot.
-/
theorem scalarKroneckerFin_sub_left [AddCommGroup R] [Module ℂ R]
    {m n : ℕ} (S T : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin (S - T) M =
      scalarKroneckerFin S M - scalarKroneckerFin T M := by
  apply CStarMatrix.ext
  intro i j
  simp only [scalarKroneckerFin_apply, CStarMatrix.sub_apply, sub_smul]

/-- Let `R` be a possibly nonunital, nonassociative semiring. `R` has a complex module structure. The
`ℂ`-scalar action on `R` is compatible with multiplication on both sides. For natural numbers `m`
and `n`, `S` and `T : CStarMatrix (Fin m) (Fin m) ℂ` and `M` and `N : CStarMatrix (Fin n) (Fin n)
R`. Multiplication after the finite-product reindex.
-/
theorem scalarKroneckerFin_mul
    [NonUnitalNonAssocSemiring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    {m n : ℕ} (S T : CStarMatrix (Fin m) (Fin m) ℂ)
    (M N : CStarMatrix (Fin n) (Fin n) R) :
    scalarKroneckerFin (S * T) (M * N) =
      scalarKroneckerFin S M * scalarKroneckerFin T N := by
  apply CStarMatrix.ext
  intro i j
  have h := congrArg
    (fun X : CStarMatrix (Fin m × Fin n) (Fin m × Fin n) R ↦
      X (finProdFinEquiv.symm i) (finProdFinEquiv.symm j))
    (scalarKronecker_mul S T M N)
  simp only [CStarMatrix.mul_apply] at h ⊢
  rw [← Equiv.sum_comp
    (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simpa only [scalarKroneckerFin_apply, scalarKronecker_apply,
    Equiv.symm_apply_apply] using h

/-- Let `R` be a complex module. `R` has a star operation. The star on `R` conjugates the complex scalar
action. For natural numbers `m` and `n`, `S : CStarMatrix (Fin m) (Fin m) ℂ` and `M : CStarMatrix
(Fin n) (Fin n) R`. Star after the finite-product reindex uses the scalar-star action.
-/
theorem scalarKroneckerFin_star
    [AddCommMonoid R] [Module ℂ R] [Star R] [StarModule ℂ R]
    {m n : ℕ} (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R) :
    star (scalarKroneckerFin S M) =
      scalarKroneckerFin (star S) (star M) := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.star_apply, scalarKroneckerFin_apply, star_smul]

/-- Let `R` be a possibly nonunital, nonassociative semiring. Let `T` be a possibly nonunital,
nonassociative semiring. `R` has a complex module structure. `R` has a star operation. `T` has a
complex module structure. `T` has a star operation. For `f : R →⋆ₙₐ[ℂ] T`, natural numbers `m` and
`n`, `S : CStarMatrix (Fin m) (Fin m) ℂ` and `M : CStarMatrix (Fin n) (Fin n) R`. Pointwise
coefficient homomorphisms commute with the finite scalar action. This is a matrix characteristic
law, not Bott group naturality.
-/
theorem scalarKroneckerFin_map
    {T : Type*}
    [NonUnitalNonAssocSemiring R] [Module ℂ R] [Star R]
    [NonUnitalNonAssocSemiring T] [Module ℂ T] [Star T]
    (f : R →⋆ₙₐ[ℂ] T)
    {m n : ℕ} (S : CStarMatrix (Fin m) (Fin m) ℂ)
    (M : CStarMatrix (Fin n) (Fin n) R) :
    CStarMatrix.map (scalarKroneckerFin S M) f =
      scalarKroneckerFin S (CStarMatrix.map M f) := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.map_apply, scalarKroneckerFin_apply, map_smul]

end

end CStarMatrix
