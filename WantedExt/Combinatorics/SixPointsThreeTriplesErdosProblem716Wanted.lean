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

/-- `ex₃(n, 𝓕)` for `𝓕` the `3`-uniform hypergraphs with `6` vertices and `3` edges: the largest
number of `3`-element subsets of `{1, …, n}` such that no `6` vertices carry `3` of them (every set
of at most `6` vertices contains at most `2` of the chosen triples). -/
noncomputable def sixThreeExtremalNumber (n : ℕ) : ℕ :=
  sSup {e | ∃ E : Finset (Finset (Fin n)), (∀ t ∈ E, t.card = 3) ∧
    (∀ S : Finset (Fin n), S.card ≤ 6 → (E.filter (· ⊆ S)).card ≤ 2) ∧ E.card = e}

/-- Erdős Problem 716 (Brown, Erdős and Sós): `ex₃(n, 𝓕) = o(n²)`. -/
def sixThreeExtremalNumberLittleO : Prop :=
  Tendsto (fun n : ℕ => (sixThreeExtremalNumber n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0)

/--
Resolved true: Ruzsa and Szemerédi proved that a `3`-uniform hypergraph on `n` vertices in which no
`6` vertices carry `3` edges has `o(n²)` edges (the `(6, 3)` theorem); erdosproblems.com/716 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #716,
https://www.erdosproblems.com/716 (status PROVED (LEAN)); resolution: I. Z. Ruzsa and E. Szemerédi,
Triple systems with no six points carrying three triangles, Combinatorics (Proc. Fifth Hungarian
Colloq., Keszthely, 1976), Vol. II (1978), 939-945, erdosproblems.com/716: 'The answer is yes,
proved by Ruzsa and Szemerédi' (the Ruzsa-Szemerédi problem), https://www.erdosproblems.com/716.
-/
public theorem_wanted sixThreeExtremalNumberLittleO_holds : sixThreeExtremalNumberLittleO

end MathlibExt.Combinatorics.SixPointsThreeTriplesErdosProblem716Wanted
