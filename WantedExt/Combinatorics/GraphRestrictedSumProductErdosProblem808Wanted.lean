/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums and products along the edges of a graph (Erdős Problem 808)

Erdős Problem 808: let `c, ε > 0` and `n` be sufficiently large. If `A ⊂ ℕ` has `|A| = n` and `G` is
any graph on `A` with at least `n^{1+c}` edges, is `max(|A +_G A|, |A ·_G A|) ≥ |A|^{1+c-ε}`, where
`A +_G A = {a + b : ab ∈ G}` and similarly for `A ·_G A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #808, https://www.erdosproblems.com/808 (status
DISPROVED). UnsolvedMath record UM-30007045 (`EP-808`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is a set of positive integers. A graph on `A` is a finite set `E` of pairs `(a, b)` with `a < b`
in `A` (one pair per edge); sums and products are taken along `E`. formal-conjectures has no
statement of this problem.
-/

/-- Erdős Problem 808: for all `c, ε > 0` and all large `n`, if `A` is a set of `n` positive
integers and `E` is a graph on `A` (edges `(a, b)` with `a < b`) with at least `n^{1+c}` edges, then
`max(|A +_E A|, |A ·_E A|) ≥ n^{1+c-ε}`. -/
def restrictedSumProductAlongGraphs : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ, 0 ∉ A → A.card = n →
    ∀ E : Finset (ℕ × ℕ), (∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2) →
      (n : ℝ) ^ (1 + c) ≤ E.card →
        (n : ℝ) ^ (1 + c - ε) ≤
          max ((E.image fun p => p.1 + p.2).card : ℝ) ((E.image fun p => p.1 * p.2).card : ℝ)

/--
Resolved false: Alon, Ruzsa and Solymosi constructed, for arbitrarily large `n`, sets of `n`
integers with graphs of `≫ n^{5/3 - o(1)}` edges along which `max(|A +_G A|, |A ·_G A|) ≪ n^{4/3 +
o(1)}`, and counterexamples in `ℕ` for every `0 < c < 1`; erdosproblems.com/808 lists the problem as
disproved. Source: T. F. Bloom, Erdős Problems, Problem #808, https://www.erdosproblems.com/808
(status DISPROVED); resolution: N. Alon, I. Ruzsa and J. Solymosi, Sums, products and ratios along
the edges of a graph, Publ. Mat. 64 (2020), 143-155, Theorem 3: for arbitrarily large m_0 there are
a set A of m ≥ m_0 integers and a graph on A with Ω(m^{5/3}/log^{1/3} m) edges such that |A +_G A| +
|A ·_G A| = O((m log m)^{4/3}), refuting their Conjecture 2 (the strong Erdős-Szemerédi conjecture);
the construction takes A = {uw/v} for positive integers u, v, w scaled by a common denominator, so A
consists of positive integers; Theorem 4 gives counterexamples A ⊂ ℕ for every 0 < c < 1,
https://web.math.princeton.edu/~nalon/PDFS/sumprodrat7.pdf.
-/
public theorem_wanted restrictedSumProductAlongGraphs_refuted : ¬ restrictedSumProductAlongGraphs

end MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808Wanted
