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

/-- Theorem 3 (quoted from Mohammad and Talukder 2020), for one length: a poset matrix of order
`m + k`, `m, k ≥ 1`, satisfies the block of `0`s property (block of `1`s property) of length `m`
iff it is the direct sum `A ⊕ B` (ordinal sum `A ⊞ B`) of poset matrices of orders `m` and `k`.
Partial: the record's version with several lengths `n₁ < ⋯ < n_m` is the iterate of this one and
is not stated separately.

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

/-- Theorem 4 (quoted from Mohammad and Talukder 2020), for two terms: if poset matrices `A` and
`B` represent posets `P` and `Q`, then the direct sum `A ⊕ B` is a poset matrix representing the
direct (disjoint) sum `P + Q` (`P ⊕ Q` with `Sum.instLE`), and the ordinal sum `A ⊞ B` is a poset
matrix representing the ordinal sum `P ⊕ₗ Q`. Partial: the record's `r`-term version is the
iterate of this one and is not stated separately; the record's `P₁ + P₁ + ⋯ + P_r` is read as
`P₁ + P₂ + ⋯ + P_r`.

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

/-- Theorem 5 (quoted from Mohammad et al. 2025): let a poset matrix `M` of order `n` represent
a poset `P`. If `M` satisfies the block of `1`s property of some length `r`, `1 ≤ r < n`, then
`P` is connected; if it satisfies the block of `0`s property of some length, then `P` is
disconnected. Connected means that every subset of `P` closed under comparability is empty or
everything; disconnected (two or more direct terms) means that some nonempty proper subset is
closed under comparability. "`M` can be relabeled" is covered because a relabeling of `M` again
represents `P`. The hypothesis `P ≇ 1` follows from `1 ≤ r < n`.

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

/-- Theorem 10, for the trees represented: a finite poset `P` with `n ≥ 3` elements that is a
rooted tree (a least element, the root, and every `Set.Iic x` a chain) is a quasi-full `t`-ary
rooted tree when every `x` has exactly `min(|Ici x| - 1, t)` children (elements covering `x`),
`Ici x` being the subtree rooted at `x`. Then (i) a quasi-full `(n-1)`-ary tree is quasi-full
`t`-ary for every `t ≥ n`, and (ii) a quasi-full `t`-ary tree with `t ≤ n - 2` is not quasi-full
`t'`-ary for any `t' ≥ n`. The record's `M ∈ 𝓜_{n,t}` (a poset matrix in a set of pairwise
nonequivalent matrices representing the quasi-full `t`-ary trees on `n` elements) is read as
"`M` represents a quasi-full `t`-ary rooted tree with `n` elements"; both parts depend only on
the represented poset, so they are stated for `P`.

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

/-- Theorem 11 (direct sum criterion, quoted from Mohammad et al. 2025): let `M` and `M'` be
poset matrices of order `n ≥ 2` and `t ≥ 2`. Suppose `M` satisfies the block of `0`s property at
the lengths `l₁ < ⋯ < l_{t-1}` (here `l : Fin (t+1) → ℕ` strictly increasing with `l 0 = 0`,
`l t = n`) which are nondecreasing inter-distant (the gaps `l_{k+1} - l_k` are nondecreasing),
and every direct term (the diagonal block on `[l_k, l_{k+1})`) satisfies the block of `1`s
property of some length; likewise `M'` with `l'`. If `l ≠ l'` (some `l_k ≠ l'_k`), then `M` and
`M'` are relabeling inequivalent. The record's hypothesis `M, M' ∈ 𝓝_{n,t}` (matrices
representing quasi-full `t`-ary rooted forests) is dropped: the claim holds for all such poset
matrices.

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
