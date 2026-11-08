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

/-- Erdős Problem 1198: for every `2`-colouring of `ℕ` there is a strictly increasing sequence
`0 < a₀ < a₁ < ⋯` such that all expressions `∑_{j<k} ∏_{i ∈ Sⱼ} aᵢ` over `k ≥ 1` pairwise
disjoint nonempty finite index sets `S₀, …, S_{k-1}`, other than the single terms `aᵢ` (`k = 1`,
`|S₀| = 1`), have the same colour. -/
def monochromaticSumsOfProducts : Prop :=
  ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
    ∀ (k : ℕ) (S : Fin k → Finset ℕ), 0 < k → (∀ j, (S j).Nonempty) →
      Pairwise (fun j j' => Disjoint (S j) (S j')) → ¬ (k = 1 ∧ ∀ j, (S j).card = 1) →
        c (∑ j, ∏ i ∈ S j, a i) = col

/--
Resolved false: Smith (SIAM J. Discrete Math. 2001, abstract) constructed, for `m ≠ n`, a two-cell
partition of `ℕ` in which no cell contains `SP_n(⟨x_t⟩) ∪ SP_m(⟨y_t⟩)` for any sequences, where
`SP_m` is the set of sums `∏_{t ∈ F₁} x_t + ⋯ + ∏_{t ∈ F_m} x_t` over finite sets `F₁ < ⋯ < F_m`.
With `x = y = a`, `m = 2` and `n = 3`, every such sum is a non-trivial expression of the problem (`k
= 2` or `k = 3` disjoint index sets), so they cannot all have one colour. erdosproblems.com/1198
attributes the counterexample to Smith (JCTA 1995) and lists the problem as disproved; Hindman's
theorem is the case where every `Sⱼ` is a singleton. Source: T. F. Bloom, Erdős Problems, Problem
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
