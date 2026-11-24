/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Order.PosetMatrix.BlockLengths
public import MathlibExt.Order.PosetMatrix.Connected
public import MathlibExt.Order.PosetMatrix.Sums
public import MathlibExt.Order.QuasiFullRootedTree
public import Mathlib.Data.Matrix.Block
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Poset matrices and quasi-full rooted trees (statements)

Statement-only targets from Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder,
*Recognition and Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28
(2025), Article 25.6.3. Poset matrices are `MetaMathlibExt.IsPosetMatrix` (Boolean, `true` for
`1`). A poset matrix `M` of order `n` *represents* a poset `P` when some `e : Fin n ≃ P` has
`e i ≤ e j ↔ M i j = true`; relabeling equivalence is `M' = M.submatrix σ σ` for a permutation
`σ`. The direct sum `M ⊕ N` and ordinal sum `M ⊞ N` are `Matrix.fromBlocks M 0 0 N` and
`Matrix.fromBlocks M 1 0 N` (all-`false` / all-`true` off-diagonal blocks), reindexed along
`finSumFinEquiv`. The block of `0`s (`1`s) property of length `r`, `1 ≤ r < n`, says that
`M i j = false` (`true`) for all `i < r ≤ j` (zero-based indices).

The arity of quasi-full rooted trees (`quasiFullTree_arity`) is proved in
`MathlibExt.Order.QuasiFullRootedTree`, which this module imports.
-/

namespace MetaMathlibExt

open Matrix

@[expose] public section

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
public theorem_wanted isPosetMatrix_block_iff_directSum_ordinalSum (m k : ℕ) (hm : 1 ≤ m)
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
            (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B))

end

end MetaMathlibExt
