/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MAXIMUM MINIMUM METRIC K-SPANNING TREE (decision version);
M. M. Halldórsson, K. Iwano, N. Katoh, and T. Tokuyama, "Finding subsets maximizing minimum
structures", SIAM Journal on Discrete Mathematics 12 (1999), 342-359,
doi:10.1137/S0895480196309791.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree

/-!
# MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete

INSTANCE: a complete graph on a set `V` of `n` vertices with a length `l(u, v) ∈ ℤ⁺` on each
edge satisfying the triangle inequality, a number `k`, and a bound `K`. QUESTION: is there a
subset `V' ⊆ V` with `|V'| = k` such that the minimum spanning tree of the subgraph induced by
`V'` has length at least `K`?

This is the decision version of the compendium's MAXIMUM MINIMUM METRIC K-SPANNING TREE,
also called REMOTE-MST: Halldórsson, Iwano, Katoh, and Tokuyama (1999) show that on metric
graphs it is NP-hard to approximate within a factor less than `2` (the compendium notes a
reduction from MAXIMUM INDEPENDENT SET: with lengths `1` on the edges of a graph and `2` on its
non-edges, the minimum spanning tree on `k` vertices has length `2 (k - 1)` exactly when they
are independent).

The lengths are an `n × n` matrix that is a metric on the vertices: zero exactly on the
diagonal (positive between distinct vertices), symmetric, and satisfying the triangle
inequality. The induced subgraph on `V'` is complete, so
its minimum spanning tree has length at least `K` exactly when every tree on the vertex set
`V'` (a `SimpleGraph` on the subtype with `SimpleGraph.IsTree`) has total edge length at least
`K`. The length of an edge `{u, v}` is read as `min (l(u, v), l(v, u))`, which is `l(u, v)` for
a symmetric matrix and makes the edge length a function of the unordered pair. `1 ≤ k ≤ n` (a
tree needs a vertex). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the length matrix as `n` rows of `n` entries
(`l(a, b)` is entry `b` of row `a`), the size `k`, and the bound `K`. -/
abbrev MaximumMinimumMetricKSpanningTreeInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- The length `l(a, b)`: entry `b` of row `a` of the matrix (`0` outside it). -/
def dist (i : MaximumMinimumMetricKSpanningTreeInstance) (a b : ℕ) : ℕ :=
  (i.2.1.getD a []).getD b 0

/-- Well-formedness of an instance: the matrix has `n` rows of `n` entries and is a metric
(`l(a, a) = 0`, `0 < l(a, b)` for `a ≠ b`, `l(a, b) = l(b, a)`, `l(a, c) ≤ l(a, b) + l(b, c)`),
and `1 ≤ k ≤ n`. -/
def WellFormed (i : MaximumMinimumMetricKSpanningTreeInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ a < i.1, dist i a a = 0) ∧ (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < dist i a b) ∧
    (∀ a < i.1, ∀ b < i.1, dist i a b = dist i b a) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1, dist i a c ≤ dist i a b + dist i b c) ∧
    1 ≤ i.2.2.1 ∧ i.2.2.1 ≤ i.1

/-- The length of an edge `{u, v}` between vertices of `V'`: `min (l(u, v), l(v, u))`. -/
def edgeLength (i : MaximumMinimumMetricKSpanningTreeInstance) (V' : Finset (Fin i.1)) :
    Sym2 V' → ℕ :=
  Sym2.lift ⟨fun a b => min (dist i a.1 b.1) (dist i b.1 a.1), fun _ _ => min_comm _ _⟩

open Classical in
/-- Some set `V'` of `k` vertices has every tree on `V'` of total edge length at least `K`. -/
def MaximumMinimumMetricKSpanningTreeFeasible
    (i : MaximumMinimumMetricKSpanningTreeInstance) : Prop :=
  ∃ V' : Finset (Fin i.1), V'.card = i.2.2.1 ∧
    ∀ T : SimpleGraph V', T.IsTree → i.2.2.2 ≤ ∑ e ∈ T.edgeFinset, edgeLength i V' e

open Classical in
/-- MAXIMUM MINIMUM METRIC K-SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def maximumMinimumMetricKSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumMinimumMetricKSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MaximumMinimumMetricKSpanningTreeFeasible i)
  | none => false

/-- **MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete.** Source: Crescenzi and Kann,
MAXIMUM MINIMUM METRIC K-SPANNING TREE; Halldórsson, Iwano, Katoh, and Tokuyama (1999). -/
public theorem_wanted maximumMinimumMetricKSpanningTree_npComplete :
    maximumMinimumMetricKSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumMinimumMetricKSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree
