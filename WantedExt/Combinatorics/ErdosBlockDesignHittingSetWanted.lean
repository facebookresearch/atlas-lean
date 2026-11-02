/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-14299518-002, question (1): for large almost-disjoint families on `[n]`,
a uniformly bounded hitting set exists.

For every fixed `0 < c < 1` there is `C` such that any family of subsets of
`Fin n`, each larger than `c√n` and pairwise intersecting in at most one
point, admits a set meeting each member in between 1 and `C` points.
Question (2) of the record (counting block-compatible sequences) is
formalized separately.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.Real.Sqrt
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosBlockDesignHittingSetWanted

/-! Source record `OWR-14299518-002`, question (1). -/

/-- **Bounded hitting sets for large partial designs (Erdős Problem 664).** The proposition that
for every real $c$ with $0 < c < 1$ there is a natural number $C$ such that for every natural
number $n$ and every family $\mathcal{B}$ of subsets of $\{0, \dots, n - 1\}$ in which each member
has more than $c\sqrt{n}$ elements and any two distinct members share at most one element, some
set $B \subseteq \{0, \dots, n - 1\}$ meets every member of $\mathcal{B}$ in at least $1$ and at
most $C$ elements. -/
def conjecture : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 →
    ∃ C : ℕ, ∀ n : ℕ, ∀ blocks : Finset (Finset (Fin n)),
      (∀ B ∈ blocks, (B.card : ℝ) > c * Real.sqrt n) →
      (∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks, B₁ ≠ B₂ → (B₁ ∩ B₂).card ≤ 1) →
      ∃ B : Finset (Fin n),
        ∀ A ∈ blocks, 0 < (B ∩ A).card ∧ (B ∩ A).card ≤ C

/--
**Large partial designs need not have uniformly bounded hitting sets.** It is not true that for
every real $c$ with $0 < c < 1$ there is a natural number $C$ such that for every natural number
$n$ and every family $\mathcal{B}$ of subsets of $\{0, \dots, n - 1\}$ in which each member has more
than $c\sqrt{n}$ elements and any two distinct members share at most one element, some set
$B \subseteq \{0, \dots, n - 1\}$ meets every member of $\mathcal{B}$ in at least $1$ and at most
$C$ elements.

Alon answered the question negatively in the source report (Oberwolfach Report 42/2025,
pp. 2249-2250, Theorem 3; also Theorem 2.1 of his note 'Blocking partial designs and
block-compatible sequences'), recorded on erdosproblems.com/664 (DISPROVED): for large prime
powers $q$ and $n = m = q^2 + q + 1$ there is a partial design of $m$ blocks of size
$> 0.4\sqrt{n}$ on $n$ points such that every set meeting all blocks meets some block in at least
$0.1 \log n$ points, so no constant $C$ works for $c \le 0.4$.

Source: N. Alon, On designs and partial designs, extended
abstract in Oberwolfach Report 42/2025 (Combinatorics, Probability and Computing), pp.
2249-2250, Theorem 3, https://doi.org/10.4171/owr/2025/42; N. Alon, Blocking partial designs and
block-compatible sequences, note, Theorem 2.1,
https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf; T. F. Bloom, Erdős Problem #664,
erdosproblems.com (status DISPROVED), https://www.erdosproblems.com/664. Moved from
`OpenConjectures/Combinatorics/ErdosBlockDesignHittingSet`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ErdosBlockDesignHittingSetWanted
