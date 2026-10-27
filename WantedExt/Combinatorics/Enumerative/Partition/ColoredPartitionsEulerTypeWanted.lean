/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Set.Card

/-!
# Colored partitions and Euler-type identities (statements)

Statement-only targets from Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and
Euler-Type Identities*, INTEGERS 26 (2026), Article A20.

A colored part `m_j` (size `m`, color `j`, `1 ≤ j ≤ m`) is the pair `(m, j) : ℕ × ℕ`. A colored
partition with distinct colors (or with fully different parts) has no repeated colored part,
so it is a finset of colored parts; a general colored partition is a multiset. A composition is
a list of positive integers; a part of size `k` colored by a composition is a pair
`(k, c) : ℕ × List ℕ`. A partition of a multiset into blocks is a multiset of nonempty
multisets whose sum (`Multiset.join`) is the multiset; a block is constant when it is
`Multiset.replicate c x`. Counts of infinite carrier types use `Set.ncard`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- For `n ≥ 0`, the number of nonempty colored partitions whose parts have size at most `n`
and pairwise different colors is `(n + 1)! - 1`. With distinct colors no colored part repeats,
so such a partition is a nonempty finset of colored parts `(m, j)`, `1 ≤ j ≤ m ≤ n`, on which
the color is injective; the paper's count excludes the empty partition.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 1 (`integers-2026-A20-thm-1`). -/
public theorem_wanted card_coloredPartitions_differentColors (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.snd).card = T.card)).card = (n + 1).factorial - 1

/-- `pf_c(n) = ∑_{p₁ > ⋯ > p_k, p₁ + ⋯ + p_k = n} p_k (p_{k-1} - 1) ⋯ (p₁ - (k - 1))`, where
`pf_c(n)` counts colored partitions of `n` with fully different parts (pairwise different sizes
and pairwise different colors). The right side lists the parts of each partition into distinct
parts increasingly as `q₀ < q₁ < ⋯` and multiplies `q_i - i`. Stated for all `n ≥ 0` (at `n = 0`
both sides are `1`); the paper says `n ≥ 1`.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 2 (`integers-2026-A20-thm-2`). -/
public theorem_wanted card_coloredPartitions_fullyDifferent (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => ∑ x ∈ T, x.1 = n ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card =
      ∑ μ ∈ Nat.Partition.distincts n,
        ((μ.parts.sort (· ≤ ·)).mapIdx fun i q => q - i).prod

/-- For `n ≥ 0`, the number of nonempty colored partitions into fully different parts (pairwise
different sizes and pairwise different colors) with parts of size at most `n` is
`B_{n+1} - 1`, with `B` the Bell numbers (`Nat.bell`).

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 3 (`integers-2026-A20-thm-3`). -/
public theorem_wanted card_coloredPartitions_fullyDifferent_le (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card = Nat.bell (n + 1) - 1

/-- The number of partitions into constant blocks of multisets of length `n` whose elements form
an initial interval `{1, …, k}` of positive integers equals the number `d_c(n)` of double
compositions of `n` (compositions in which each summand `m` is colored by a partition of `m`),
`d_c(n) = ∑_{c ⊨ n} ∏_i p(c_i)`. Both the multiset and its partition vary on the left.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 4 (`integers-2026-A20-thm-4`). -/
public theorem_wanted ncard_constantBlockPartitions_eq_doubleCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = n ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => Fintype.card (Nat.Partition m)).prod

/-- The number of partitions into pairwise distinct constant blocks of multisets of length `n`
whose elements form an initial interval `{1, …, k}` of positive integers equals the number of
compositions of `n` in which each summand `m` is colored by a partition of `m` into distinct
parts, `∑_{c ⊨ n} ∏_i q(c_i)`.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 1 (`integers-2026-A20-cor-1`). -/
public theorem_wanted ncard_distinctConstantBlockPartitions_eq_coloredCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = n ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => (Nat.Partition.distincts m).card).prod

/-- Generalized Euler partition theorem. Let `S` be an even-admissible set of compositions
(lists of positive integers; doubling every summand stays in `S`, and halving every summand of
an all-even member stays in `S`). For `n ≥ 0`, the number of partitions of `n` into distinct
colored parts, each part of size `k` colored by a member of `S` of size `k` (resp. of size at
most `k`), equals the number of such partitions (repetition allowed) in which no even part is
colored by a composition with all summands even. Distinct means distinct pairs (size, color).

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 5 (`integers-2026-A20-thm-5`). -/
public theorem_wanted generalized_euler_partition_theorem (S : Set (List ℕ))
    (hS : ∀ c ∈ S, ∀ x ∈ c, 0 < x) (hdouble : ∀ c ∈ S, c.map (2 * ·) ∈ S)
    (hhalf : ∀ c ∈ S, (∀ x ∈ c, Even x) → c.map (· / 2) ∈ S) (n : ℕ) :
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum = x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum = x.1 ∧
        (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧ (M.map Prod.fst).sum = n}.ncard ∧
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ x.2 ∈ S ∧ x.2.sum ≤ x.1 ∧
        (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧ (M.map Prod.fst).sum = n}.ncard

/-- For `ℓ ≥ 0` and `n ≥ 0`, the number of partitions of `n` into distinct colored parts, each
part of size `k` colored by an `ℓ`-restricted composition of `k` (at most `ℓ` summands), equals
the number of such partitions (repetition allowed) in which no even part is colored by an
`ℓ`-restricted composition with all summands even. Distinct means distinct pairs (size, color).

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 3 (`integers-2026-A20-cor-3`). -/
public theorem_wanted euler_partition_theorem_restrictedCompositions (ℓ n : ℕ) :
    {M : Multiset (ℕ × List ℕ) | M.Nodup ∧ (∀ x ∈ M, 0 < x.1 ∧ (∀ y ∈ x.2, 0 < y) ∧
        x.2.length ≤ ℓ ∧ x.2.sum = x.1) ∧ (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × List ℕ) | (∀ x ∈ M, 0 < x.1 ∧ (∀ y ∈ x.2, 0 < y) ∧
        x.2.length ≤ ℓ ∧ x.2.sum = x.1 ∧ (Even x.1 → ¬ ∀ y ∈ x.2, Even y)) ∧
        (M.map Prod.fst).sum = n}.ncard

/-- For `n ≥ 0`, the number of colored partitions of `n` with different parts (no colored part
`m_j`, `1 ≤ j ≤ m`, repeated) equals the number of colored partitions of `n` in which no even
part has an even color, and also the number in which no even part has an odd color.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 4 (`integers-2026-A20-cor-4`). -/
public theorem_wanted coloredPartitions_differentParts_eq_restrictedColors (n : ℕ) :
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → ¬ Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard ∧
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard

end

end MetaMathlibExt
