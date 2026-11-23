/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent Schur triples in triangle-free graphs (Erdős Problem 895)

Erdős Problem 895 (Erdős and Hajnal): is it true that, for all sufficiently large `n`, if `G` is a
triangle-free graph on `{1, …, n}` then there must exist three independent points `a, b, a + b`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeSchurTripleErdosProblem895Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #895, https://www.erdosproblems.com/895 (status
PROVED). UnsolvedMath record UM-30007073 (`EP-895`), dataset ulamai/UnsolvedMath v1.8.0.

The three points are distinct, so `a ≠ b` (and `a, b ≥ 1`). The graph is a triangle-free graph on
`ℕ`; only its vertices in `{1, …, n}` matter, so this is equivalent to a triangle-free graph on `{1,
…, n}`. The resolution is a computation: by monotonicity in `n` it reduces to the single case `n =
18`. Compared with the formal-conjectures statement `ErdosProblems/895.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 895 (Erdős and Hajnal): for all large `n`, every triangle-free graph on
`{1, …, n}` has pairwise non-adjacent vertices `a`, `b`, `a + b` with `a ≠ b`. -/
def triangleFreeIndependentSchurTriple : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph ℕ, G.CliqueFree 3 →
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a ≠ b ∧ a + b ≤ n ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a (a + b) ∧ ¬ G.Adj b (a + b)

/--
Resolved true: Barber verified with a SAT solver that every triangle-free graph on `{1, …, n}` with
`n ≥ 18` has independent points `a, b, a + b`; erdosproblems.com/895 lists the problem as proved
(Hajnal's independent Hindman set question remains open). Source: T. F. Bloom, Erdős Problems,
Problem #895, https://www.erdosproblems.com/895 (status PROVED); resolution: P. Barber, personal
communication (SAT solver verification), reported on erdosproblems.com/895, erdosproblems.com/895:
the stated problem has been resolved by Barber, who verified using a SAT solver that this is true
for all n ≥ 18, https://www.erdosproblems.com/895.
-/
public theorem_wanted triangleFreeIndependentSchurTriple_holds : triangleFreeIndependentSchurTriple

end MathlibExt.GraphTheory.TriangleFreeSchurTripleErdosProblem895Wanted
