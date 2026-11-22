/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The `(6, 3)` problem (Erdős Problem 716)

Erdős Problem 716 (Brown, Erdős and Sós): let `𝓕` be the family of all `3`-uniform hypergraphs with
`6` vertices and `3` edges. Is it true that `ex₃(n, 𝓕) = o(n²)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #716, https://www.erdosproblems.com/716 (status PROVED
(LEAN)). UnsolvedMath record UM-30006989 (`EP-716`), dataset ulamai/UnsolvedMath v1.8.0.

A `3`-uniform hypergraph on `{1, …, n}` contains a member of `𝓕` iff some `6` vertices carry `3` of
its edges; `ex₃(n, 𝓕)` is the largest number of triples with every set of at most `6` vertices
containing at most `2` of them (for `n < 6` this differs from the literal definition, which does not
affect `o(n²)`). `o(n²)` is `ex₃(n, 𝓕) / n² → 0`. Compared with the formal-conjectures statement
`ErdosProblems/716.lean` (equivalent; no code imported).
-/

open Filter Topology

/-- **The (6, 3) extremal number.** For $n \in \mathbb{N}$, $\mathrm{ex}_3(n)$ is the largest
number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$ of these
points contains at most $2$ of the chosen subsets.

For $n \ge 6$ this is the extremal number $\mathrm{ex}_3(n, \mathcal{F})$ of the family
$\mathcal{F}$ of $3$-uniform hypergraphs with $6$ vertices and $3$ edges, since a set of triples
contains a member of $\mathcal{F}$ exactly when some $6$ points carry $3$ of the triples. -/
noncomputable def sixThreeExtremalNumber (n : ℕ) : ℕ :=
  sSup {e | ∃ E : Finset (Finset (Fin n)), (∀ t ∈ E, t.card = 3) ∧
    (∀ S : Finset (Fin n), S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) ∧ E.card = e}

/-- **The Brown–Erdős–Sós (6, 3) conjecture.** For $n \in \mathbb{N}$ let $\mathrm{ex}_3(n)$ be
the largest number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$
of these points contains at most $2$ of the chosen subsets. The conjecture (Erdős Problem 716) is
the proposition that $\mathrm{ex}_3(n) / n^2 \to 0$ as $n \to \infty$, that is,
$\mathrm{ex}_3(n) = o(n^2)$. -/
def sixThreeExtremalNumberLittleO : Prop :=
  Tendsto (fun n : ℕ => (sixThreeExtremalNumber n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0)

/-- **The Ruzsa–Szemerédi (6, 3) theorem.** For $n \in \mathbb{N}$ let $\mathrm{ex}_3(n)$ be the
largest number of $3$-element subsets of $\{1, \dots, n\}$ such that every set of at most $6$ of
these points contains at most $2$ of the chosen subsets. Then $\mathrm{ex}_3(n) / n^2 \to 0$ as
$n \to \infty$, that is, $\mathrm{ex}_3(n) = o(n^2)$.

Source: T. F. Bloom, Erdős Problems, Problem #716,
https://www.erdosproblems.com/716 (status PROVED (LEAN)); resolution: I. Z. Ruzsa and E. Szemerédi,
Triple systems with no six points carrying three triangles, Combinatorics (Proc. Fifth Hungarian
Colloq., Keszthely, 1976), Vol. II (1978), 939-945, erdosproblems.com/716: 'The answer is yes,
proved by Ruzsa and Szemerédi' (the Ruzsa-Szemerédi problem), https://www.erdosproblems.com/716.
-/
public theorem_wanted sixThreeExtremalNumberLittleO_holds : sixThreeExtremalNumberLittleO

end MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted
