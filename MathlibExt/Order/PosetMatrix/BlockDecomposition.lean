/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
public import MathlibExt.Order.PosetMatrix

/-!
# Block decomposition of a poset matrix

A constant upper-right block characterizes the direct and ordinal sums of poset matrices.
-/

namespace MetaMathlibExt

open Matrix

set_option linter.unusedVariables false in
/-- **Block decomposition of a poset matrix.** Let $m, k \ge 1$ and let $M$ be a poset matrix of
order $m + k$, a Boolean matrix with rows and columns indexed by $0, \dots, m + k - 1$. Then
$M_{ij}$ is false for all $i < m \le j$ if and only if there are poset matrices $A$ of order $m$
and $B$ of order $k$ such that $M$ is their direct sum: $M_{ij} = A_{ij}$ for $i, j < m$,
$M_{m+i, m+j} = B_{ij}$ for $i, j < k$, and every other entry of $M$ is false. Likewise $M_{ij}$
is true for all $i < m \le j$ if and only if there are poset matrices $A$ of order $m$ and $B$ of
order $k$ such that $M$ is their ordinal sum: the same diagonal blocks, $M_{ij}$ true for all
$i < m \le j$, and $M_{ij}$ false for all $j < m \le i$.

Only one block length is stated; the version with several lengths $n_1 < \dots < n_r$ follows by
iterating it.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 3 (`jis-2025-25.6.3-thm-3`). -/
public theorem isPosetMatrix_block_iff_directSum_ordinalSum (m k : ℕ) (hm : 1 ≤ m)
    (hk : 1 ≤ k) (M : Matrix (Fin (m + k)) (Fin (m + k)) Bool) (hM : IsPosetMatrix (m + k) M) :
    ((∀ i j : Fin (m + k), (i : ℕ) < m → m ≤ (j : ℕ) → M i j = false) ↔
      ∃ A : Matrix (Fin m) (Fin m) Bool, ∃ B : Matrix (Fin k) (Fin k) Bool,
        IsPosetMatrix m A ∧ IsPosetMatrix k B ∧
          M = reindex finSumFinEquiv finSumFinEquiv
            (fromBlocks A (Matrix.of fun _ _ => false) (Matrix.of fun _ _ => false) B)) ∧
    ((∀ i j : Fin (m + k), (i : ℕ) < m → m ≤ (j : ℕ) → M i j = true) ↔
      ∃ A : Matrix (Fin m) (Fin m) Bool, ∃ B : Matrix (Fin k) (Fin k) Bool,
        IsPosetMatrix m A ∧ IsPosetMatrix k B ∧
          M = reindex finSumFinEquiv finSumFinEquiv
            (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B)) := by
  have restrict {n : ℕ} (f : Fin n → Fin (m + k)) (hf : StrictMono f) :
      IsPosetMatrix n (M.submatrix f f) :=
    ⟨fun i j hij => hM.upper _ _ (hf hij), fun i => hM.diagonal (f i),
      fun i j l => hM.transitive (f i) (f j) (f l)⟩
  have block (b : Bool) :
      (∀ i j : Fin (m + k), i.val < m → m ≤ j.val → M i j = b) ↔
        ∃ A : Matrix (Fin m) (Fin m) Bool, ∃ B : Matrix (Fin k) (Fin k) Bool,
          IsPosetMatrix m A ∧ IsPosetMatrix k B ∧
            M = reindex finSumFinEquiv finSumFinEquiv
              (fromBlocks A (Matrix.of fun _ _ => b) (Matrix.of fun _ _ => false) B) := by
    constructor
    · intro h
      refine ⟨_, _, restrict _ (Fin.strictMono_castAdd k), restrict _ (Fin.strictMono_natAdd m), ?_⟩
      ext i j
      induction i using Fin.addCases <;> induction j using Fin.addCases
      · simp [submatrix]
      · rename_i i j
        simpa [submatrix] using h _ _ i.isLt (Nat.le_add_right m j.val)
      · rename_i i j
        simpa [submatrix] using hM.upper _ _ (j.isLt.trans_le (Nat.le_add_right m i.val))
      · simp [submatrix]
    · rintro ⟨A, B, _, _, rfl⟩ i j
      induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [submatrix]
  exact ⟨block false, block true⟩

end MetaMathlibExt
