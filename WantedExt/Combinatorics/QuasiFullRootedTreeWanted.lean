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

/-- **Direct and ordinal sums of poset matrices represent sums of posets.** A poset matrix $M$ of
order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, represents a
partial order $P$ when there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such that
$e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $A$ and $B$ be poset matrices of orders $m$
and $k$ representing partial orders $P$ and $Q$. Let $A \oplus B$ and $A \boxplus B$ be the
matrices $N$ of order $m + k$ with $N_{ij} = A_{ij}$ for $i, j < m$, $N_{m+i, m+j} = B_{ij}$ for
$i, j < k$, and $N_{ij}$ false for all $j < m \le i$, where $N_{ij}$ for $i < m \le j$ is false
in $A \oplus B$ and true in $A \boxplus B$. Then $A \oplus B$ is a poset matrix representing the
disjoint sum $P + Q$, in which no element of $P$ is comparable with an element of $Q$, and
$A \boxplus B$ is a poset matrix representing the ordinal sum $P \oplus Q$, in which every
element of $P$ lies below every element of $Q$.

Only sums of two terms are stated; sums of $r$ terms follow by iterating.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 4 (`jis-2025-25.6.3-thm-4`). -/
public theorem_wanted directSum_ordinalSum_represents {P Q : Type*} [PartialOrder P]
    [PartialOrder Q] (m k : ℕ) (A : Matrix (Fin m) (Fin m) Bool) (B : Matrix (Fin k) (Fin k) Bool)
    (hA : IsPosetMatrix m A) (hB : IsPosetMatrix k B) (eA : Fin m ≃ P)
    (heA : ∀ i j, eA i ≤ eA j ↔ A i j = true) (eB : Fin k ≃ Q)
    (heB : ∀ i j, eB i ≤ eB j ↔ B i j = true) :
    (IsPosetMatrix (m + k) (reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks A (Matrix.of fun _ _ => false) (Matrix.of fun _ _ => false) B)) ∧
      ∃ e : Fin (m + k) ≃ P ⊕ Q, ∀ i j, e i ≤ e j ↔
        reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A (Matrix.of fun _ _ => false) (Matrix.of fun _ _ => false) B) i j =
            true) ∧
    (IsPosetMatrix (m + k) (reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B)) ∧
      ∃ e : Fin (m + k) ≃ P ⊕ₗ Q, ∀ i j, e i ≤ e j ↔
        reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A (Matrix.of fun _ _ => true) (Matrix.of fun _ _ => false) B) i j = true)

end

end MetaMathlibExt
