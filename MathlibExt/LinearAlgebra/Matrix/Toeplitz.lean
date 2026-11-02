/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Order

namespace MetaMathlibExt

@[expose]
public section

/-- **Toeplitz matrix.** A real $(n+1) \times (n+1)$ matrix $A = (a_{ij})$, with rows and columns
indexed by $\{0, \dots, n\}$, is Toeplitz if there is a function $c : \mathbb{Z} \to \mathbb{R}$
such that $a_{ij} = c(i - j)$ for all $i, j$. Equivalently, $A$ is constant along each of its
diagonals.

Only the values $c(k)$ with $-n \le k \le n$ enter the condition, so this is the same as asking
for real coefficients $c_{-n}, \dots, c_n$.

Concept id: `jis_term_af166143477154e55b2be88d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex
Source SHA-256: `f9b167508df14b8b3fa97556d04b3fd2fca3fc7939a1c23904e576e73f0a58c2`.
Definition block SHA-256: `17bf8967c8c4965db527869b4efe74d630e63681258d740ad2f98a54e2ed8008`. -/
def IsToeplitzMatrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∃ c : ℤ → ℝ, ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))

/-- **Symmetric Toeplitz matrix.** A real $(n+1) \times (n+1)$ matrix $A = (a_{ij})$, with rows
and columns indexed by $\{0, \dots, n\}$, is symmetric Toeplitz if there is a function
$c : \mathbb{Z} \to \mathbb{R}$ such that $c(-k) = c(k)$ for every integer $k$ and
$a_{ij} = c(i - j)$ for all $i, j$.

Concept id: `jis_term_af166143477154e55b2be88d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex
Source SHA-256: `f9b167508df14b8b3fa97556d04b3fd2fca3fc7939a1c23904e576e73f0a58c2`.
Definition block SHA-256: `17bf8967c8c4965db527869b4efe74d630e63681258d740ad2f98a54e2ed8008`. -/
def IsSymmetricToeplitzMatrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∃ c : ℤ → ℝ, (∀ k : ℤ, c (-k) = c k) ∧
    ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))

/-- **Toeplitz matrices from coefficients.** Let $A = (a_{ij})$ be a real $(n+1) \times (n+1)$
matrix with rows and columns indexed by $\{0, \dots, n\}$. If $c : \mathbb{Z} \to \mathbb{R}$
satisfies $a_{ij} = c(i - j)$ for all $i, j$, then $A$ is a Toeplitz matrix. -/
theorem isToeplitzMatrix_of_witness {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : ℤ → ℝ}
    (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) : IsToeplitzMatrix A :=
  ⟨c, h⟩

/-- **Symmetric Toeplitz matrices from even coefficients.** Let $A = (a_{ij})$ be a real
$(n+1) \times (n+1)$ matrix with rows and columns indexed by $\{0, \dots, n\}$. If
$c : \mathbb{Z} \to \mathbb{R}$ satisfies $c(-k) = c(k)$ for every integer $k$ and
$a_{ij} = c(i - j)$ for all $i, j$, then $A$ is a symmetric Toeplitz matrix. -/
theorem isSymmetricToeplitzMatrix_of_witness {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : ℤ → ℝ}
    (hsym : ∀ k : ℤ, c (-k) = c k)
    (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) : IsSymmetricToeplitzMatrix A :=
  ⟨c, hsym, h⟩

/-- **Symmetric Toeplitz matrices are Toeplitz.** Every real $(n+1) \times (n+1)$ symmetric
Toeplitz matrix is a Toeplitz matrix. -/
theorem IsSymmetricToeplitzMatrix.isToeplitz {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsSymmetricToeplitzMatrix A) : IsToeplitzMatrix A := by
  obtain ⟨c, _, hr⟩ := h
  exact ⟨c, hr⟩

/-- **Symmetric Toeplitz matrices are symmetric.** If $A = (a_{ij})$ is a real
$(n+1) \times (n+1)$ symmetric Toeplitz matrix, with rows and columns indexed by
$\{0, \dots, n\}$, then $a_{ij} = a_{ji}$ for all $i, j$. -/
theorem IsSymmetricToeplitzMatrix.entry_comm {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (h : IsSymmetricToeplitzMatrix A) (i j : Fin (n + 1)) : A i j = A j i := by
  obtain ⟨c, hsym, hr⟩ := h
  have hdiff : (i.val : ℤ) - (j.val : ℤ) = -((j.val : ℤ) - (i.val : ℤ)) := by
    omega
  rw [hr i j, hr j i, hdiff, hsym]

end

end MetaMathlibExt
