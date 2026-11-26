/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Poset matrix.** An $n \times n$ Boolean matrix $M$, with rows and columns indexed by
$\{0, \dots, n-1\}$, is an upper-triangular $(0, 1)$-poset matrix when its entries strictly
below the main diagonal are false ($M_{ij}$ is false whenever $j < i$), its diagonal entries
$M_{ii}$ are true, and its true entries are transitive: if $M_{ij}$ and $M_{jk}$ are true,
then $M_{ik}$ is true.

Source: JIS `mohammad3.tex`, lines 171–176, SHA-256
`839f29b85b01af033998ae2ca01fb12acb8b055b72ed095859474eb3f746a2b8`. -/
def IsPosetMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool) : Prop :=
  (∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false) ∧
    (∀ i : Fin n, M i i = true) ∧
    (∀ i j k : Fin n, M i j = true → M j k = true → M i k = true)

/-- **Relation represented by a Boolean matrix.** Let $M$ be an $n \times n$ Boolean matrix
with rows and columns indexed by $\{0, \dots, n-1\}$. The relation represented by $M$
relates index $i$ to index $j$ exactly when the entry $M_{ij}$ is true.

The matrix $M$ is arbitrary; it need not be a poset matrix. -/
def IsPosetMatrix.Rel {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool)
    (i j : Fin n) : Prop :=
  M i j = true

/-- **Poset matrices are upper triangular.** If $M$ is an $n \times n$ poset matrix, then
$M_{ij}$ is false for all indices $i, j < n$ with $j < i$. -/
theorem IsPosetMatrix.upper {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) :
    ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = false :=
  h.1

/-- **Diagonal entries of a poset matrix.** If $M$ is an $n \times n$ poset matrix, then
$M_{ii}$ is true for every index $i < n$. -/
theorem IsPosetMatrix.diagonal {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) : ∀ i : Fin n, M i i = true :=
  h.2.1

/-- **Transitivity of the true entries of a poset matrix.** If $M$ is an $n \times n$ poset
matrix, then for all indices $i, j, k < n$, if $M_{ij}$ and $M_{jk}$ are true, then $M_{ik}$
is true. -/
theorem IsPosetMatrix.transitive {n : ℕ}
    {M : Matrix (Fin n) (Fin n) Bool} (h : IsPosetMatrix n M) :
    ∀ i j k : Fin n, M i j = true → M j k = true → M i k = true :=
  h.2.2

/-- **The relation of a poset matrix is reflexive.** If $M$ is an $n \times n$ poset matrix,
then the relation represented by $M$ relates every index $i < n$ to itself. -/
theorem IsPosetMatrix.rel_refl {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) (i : Fin n) :
    IsPosetMatrix.Rel M i i :=
  h.2.1 i

/-- **The relation of a poset matrix is transitive.** If $M$ is an $n \times n$ poset matrix
and $i, j, k < n$ are indices such that the relation represented by $M$ relates $i$ to $j$
and $j$ to $k$, then it relates $i$ to $k$. -/
theorem IsPosetMatrix.rel_trans {n : ℕ} {M : Matrix (Fin n) (Fin n) Bool}
    (h : IsPosetMatrix n M) (i j k : Fin n)
    (hij : IsPosetMatrix.Rel M i j)
    (hjk : IsPosetMatrix.Rel M j k) :
    IsPosetMatrix.Rel M i k :=
  h.2.2 i j k hij hjk

end

end MetaMathlibExt
