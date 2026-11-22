/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic sums of products in two-colourings of the integers (Erdős Problem 1198)

Erdős Problem 1198: if `ℕ` is `2`-coloured, must there be an infinite set `A = {a₁ < a₂ < ⋯}` such
that all expressions `∏_{i ∈ S₁} aᵢ + ⋯ + ∏_{i ∈ S_k} aᵢ` for disjoint `S₁, …, S_k` (excluding the
trivial expressions `aᵢ`) have the same colour?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1198, https://www.erdosproblems.com/1198 (status
DISPROVED). UnsolvedMath record UM-30007239 (`EP-1198`), dataset ulamai/UnsolvedMath v1.8.0.

The index sets are nonempty, finite and pairwise disjoint, `k ≥ 1`, and the excluded trivial
expressions are `k = 1` with `|S₁| = 1`; the elements `aᵢ` themselves need not have that colour (as
discussed on the problem page). The elements are positive integers. Compared with the
formal-conjectures statement `ErdosProblems/1198.lean` (equivalent; no code imported).
-/

open Finset

/-- **Erdős Problem 1198: monochromatic sums of products.** This is the statement that for every
colouring $c : \mathbb{N} \to \{0, 1\}$ there are a strictly increasing sequence
$0 < a_0 < a_1 < \cdots$ of natural numbers and a colour $\gamma \in \{0, 1\}$ such that
$c\bigl(\sum_{j < k} \prod_{i \in S_j} a_i\bigr) = \gamma$ for every $k \ge 1$ and all pairwise
disjoint nonempty finite sets $S_0, \dots, S_{k-1} \subseteq \mathbb{N}$, except when $k = 1$ and
$S_0$ has exactly one element. -/
def monochromaticSumsOfProducts : Prop :=
  ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
    ∀ (k : ℕ) (S : Fin k → Finset ℕ), 0 < k → (∀ j, (S j).Nonempty) →
      Pairwise (fun j j' => Disjoint (S j) (S j')) → ¬ (k = 1 ∧ ∀ j, (S j).card = 1) →
        c (∑ j, ∏ i ∈ S j, a i) = col

/--
**Smith's counterexample to Erdős Problem 1198.** There is a colouring
$c : \mathbb{N} \to \{0, 1\}$ such that for every strictly increasing sequence
$0 < a_0 < a_1 < \cdots$ of natural numbers, the numbers $\sum_{j < k} \prod_{i \in S_j} a_i$,
taken over all $k \ge 1$ and all pairwise disjoint nonempty finite sets
$S_0, \dots, S_{k-1} \subseteq \mathbb{N}$ other than those with $k = 1$ and $|S_0| = 1$, do not
all have the same colour.

Smith (SIAM J. Discrete Math. 2001) constructed, for $m \ne n$, a two-cell partition of
$\mathbb{N}$ in which no cell contains $SP_n(x) \cup SP_m(y)$ for any sequences $x$ and $y$, where
$SP_m(x)$ is the set of sums $\prod_{t \in F_1} x_t + \cdots + \prod_{t \in F_m} x_t$ over nonempty
finite sets $F_1 < \cdots < F_m$ (here $F < F'$ means that every element of $F$ is less than every
element of $F'$). Taking $x = y = a$, $m = 2$ and $n = 3$, every such sum is one of the numbers
above, so they cannot all have one colour. Hindman's theorem is the case where every $S_j$ is a
singleton.

Source: T. F. Bloom, Erdős Problems, Problem
#1198, https://www.erdosproblems.com/1198 (status DISPROVED); resolution: G. L. Smith, Partitions
and (m and n) sums of products, J. Combin. Theory Ser. A 72 (1995), 77-94; G. L. Smith, Partitions
and (m and n) sums of products - two cell partition, SIAM J. Discrete Math. 14 (2001), 356-369,
erdosproblems.com/1198: a counterexample was provided by Smith [Sm95]; the two-colour counterexample
is the 2001 paper (abstract: for m ≠ n, a two cell partition of ℕ such that neither cell contains
SP_n(⟨x_t⟩) ∪ SP_m(⟨y_t⟩), SP_m the sums of m increasing products),
https://doi.org/10.1137/S0895480198349014.
-/
public theorem_wanted monochromaticSumsOfProducts_refuted : ¬ monochromaticSumsOfProducts

end MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted
