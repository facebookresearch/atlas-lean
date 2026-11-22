/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Order.PosetMatrix
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

/-- **Block properties decide connectedness of the represented poset.** Let $M$ be a poset matrix
of order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, that
represents a partial order $P$: there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such
that $e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $1 \le r < n$. If $M_{ij}$ is true for
all $i < r \le j$ (the block of $1$s property of length $r$), then $P$ is connected: every subset
$S$ of $P$ such that $x \in S \iff y \in S$ whenever $x \le y$ is empty or all of $P$. If
$M_{ij}$ is false for all $i < r \le j$ (the block of $0$s property of length $r$), then $P$ is
disconnected: some nonempty subset $S$ of $P$ with nonempty complement satisfies
$x \in S \iff y \in S$ whenever $x \le y$.

Since a relabeling of $M$ represents the same poset, this also covers matrices that satisfy a
block property after relabeling.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 5 (`jis-2025-25.6.3-thm-5`). -/
public theorem_wanted connected_or_disconnected_of_block_property {P : Type*} [PartialOrder P]
    (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool) (hM : IsPosetMatrix n M) (e : Fin n ≃ P)
    (he : ∀ i j, e i ≤ e j ↔ M i j = true) (r : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r < n) :
    ((∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → M i j = true) →
      ∀ S : Set P, (∀ x y : P, x ≤ y → (x ∈ S ↔ y ∈ S)) → S = ∅ ∨ S = Set.univ) ∧
    ((∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → M i j = false) →
      ∃ S : Set P, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ x y : P, x ≤ y → (x ∈ S ↔ y ∈ S))

/-- **Arity of quasi-full rooted trees.** Let $P$ be a finite partial order with $n \ge 3$
elements that is a rooted tree: $P$ has a least element and, for every $x \in P$, the elements
below $x$ form a chain. For a natural number $t$, call $P$ quasi-full $t$-ary when every $x \in P$
is covered by exactly $\min(|U_x| - 1, t)$ elements of $P$, where $U_x = \{y \in P : x \le y\}$.
Then (i) if $P$ is quasi-full $(n - 1)$-ary, it is quasi-full $t$-ary for every $t \ge n$; and
(ii) if $P$ is quasi-full $t$-ary for some $t \le n - 2$, it is not quasi-full $t'$-ary for any
$t' \ge n$.

The source states this for poset matrices representing quasi-full $t$-ary rooted trees; both
parts depend only on the represented poset.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 10 (`jis-2025-25.6.3-thm-10`). -/
public theorem_wanted quasiFullTree_arity {P : Type*} [PartialOrder P] [Fintype P]
    (hn : 3 ≤ Fintype.card P) (hroot : ∃ ρ : P, ∀ x, ρ ≤ x)
    (hchain : ∀ x : P, IsChain (· ≤ ·) (Set.Iic x)) :
    ((∀ x : P, Nat.card {y : P // x ⋖ y} =
        min (Nat.card (Set.Ici x) - 1) (Fintype.card P - 1)) →
      ∀ t, Fintype.card P ≤ t →
        ∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t) ∧
    (∀ t, t ≤ Fintype.card P - 2 →
      (∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t) →
        ∀ t', Fintype.card P ≤ t' →
          ¬ ∀ x : P, Nat.card {y : P // x ⋖ y} = min (Nat.card (Set.Ici x) - 1) t')

/-- **Direct sum criterion for relabeling inequivalence.** Let $n, t \ge 2$ and let
$M$ and $M'$ be poset matrices of order $n$, Boolean matrices with rows and columns indexed by
$0, \dots, n - 1$. Let $0 = l_0 < l_1 < \dots < l_t = n$ be such that the gaps $l_{k+1} - l_k$ are
nondecreasing in $k$. Suppose that for every $k \le t$, $M_{ij}$ is false for all $i < l_k \le j$,
and that for every $k < t$ there is $s \ge 1$ with $l_k + s < l_{k+1}$ such that $M_{ij}$ is true
for all $i, j$ with $l_k \le i < l_k + s \le j < l_{k+1}$. Suppose the same of $M'$ with a sequence
$0 = l'_0 < l'_1 < \dots < l'_t = n$ whose gaps are nondecreasing. If $l_k \ne l'_k$ for some $k$,
then $M$ and $M'$ are not relabeling equivalent: there is no permutation $\sigma$ of
$\{0, \dots, n - 1\}$ with $M'_{ij} = M_{\sigma(i) \sigma(j)}$ for all $i, j$.

The source assumes in addition that $M$ and $M'$ represent quasi-full $t$-ary rooted forests; the
statement holds without that assumption.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 11 (`jis-2025-25.6.3-thm-11`). -/
public theorem_wanted not_relabel_equiv_of_blockLengths_ne (n t : ℕ) (hn : 2 ≤ n) (ht : 2 ≤ t)
    (M M' : Matrix (Fin n) (Fin n) Bool) (hM : IsPosetMatrix n M) (hM' : IsPosetMatrix n M')
    (l l' : Fin (t + 1) → ℕ)
    (hl : l 0 = 0 ∧ l (Fin.last t) = n ∧ StrictMono l ∧
      Monotone fun k : Fin t => l k.succ - l k.castSucc)
    (hl' : l' 0 = 0 ∧ l' (Fin.last t) = n ∧ StrictMono l' ∧
      Monotone fun k : Fin t => l' k.succ - l' k.castSucc)
    (hzero : ∀ k : Fin (t + 1), ∀ i j : Fin n, (i : ℕ) < l k → l k ≤ (j : ℕ) → M i j = false)
    (hzero' : ∀ k : Fin (t + 1), ∀ i j : Fin n, (i : ℕ) < l' k → l' k ≤ (j : ℕ) →
      M' i j = false)
    (hone : ∀ k : Fin t, ∃ s, 1 ≤ s ∧ l k.castSucc + s < l k.succ ∧
      ∀ i j : Fin n, l k.castSucc ≤ (i : ℕ) → (i : ℕ) < l k.castSucc + s →
        l k.castSucc + s ≤ (j : ℕ) → (j : ℕ) < l k.succ → M i j = true)
    (hone' : ∀ k : Fin t, ∃ s, 1 ≤ s ∧ l' k.castSucc + s < l' k.succ ∧
      ∀ i j : Fin n, l' k.castSucc ≤ (i : ℕ) → (i : ℕ) < l' k.castSucc + s →
        l' k.castSucc + s ≤ (j : ℕ) → (j : ℕ) < l' k.succ → M' i j = true)
    (hne : l ≠ l') :
    ¬ ∃ σ : Equiv.Perm (Fin n), M' = M.submatrix σ σ

end

end MetaMathlibExt
