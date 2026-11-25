/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST PATH WITH FORBIDDEN PAIRS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), entry SHORTEST PATH WITH FORBIDDEN PAIRS in its graph theory section (decision
version);
V. Kann, "Polynomially bounded minimization problems that are hard to approximate", Nordic
Journal of Computing 1 (1994), 317-331 (conference version: ICALP 1993, LNCS 700, 52-63,
doi:10.1007/3-540-56939-1_61);
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of program
test paths", IEEE Transactions on Software Engineering SE-2(3) (1976), 227-231,
doi:10.1109/TSE.1976.233819;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestPathWithForbiddenPairs

/-!
# SHORTEST PATH WITH FORBIDDEN PAIRS is NP-complete

INSTANCE: a graph `G = (V, E)`, a collection `C = {(a₁, b₁), …, (aₘ, bₘ)}` of pairs of vertices
from `V`, an initial vertex `s ∈ V`, a final vertex `f ∈ V`, and a positive integer `K`.
QUESTION: is there a simple path from `s` to `f` in `G` that contains at most one vertex from
each pair in `C` and has at most `K` edges?

This is the decision version of the compendium's SHORTEST PATH WITH FORBIDDEN PAIRS (undirected
graph, measure the number of edges of the path). Kann (1994) proves the optimization problem NPO
PB-complete and attributes the definition and the NP-completeness of the shortest and longest
path with forbidden pairs problems to Gabow, Maheshwari and Osterweil (1976); Kann's measure
counts the vertices of the path, one more than its edges. The existence question without a
length bound is Garey and Johnson's PATH WITH FORBIDDEN PAIRS ([GT54],
`PathWithForbiddenPairsWanted`, directed graphs). The undirected question is NP-hard as well:
for a 3-CNF formula with clauses `C₁, …, Cₘ` (`m ≥ 1`), take vertices `c₀, …, cₘ` and, for each
literal occurrence in `Cⱼ`, one vertex adjacent to `cⱼ₋₁` and `cⱼ`; with `s = c₀`, `f = cₘ`, the
pairs of occurrences of complementary literals, and `K = 2m`, every simple `s`-`f` path passes
`c₀, …, cₘ` in order through one occurrence per clause, so such a path exists if and only if the
formula is satisfiable. The companion maximization problem is
`LongestPathWithForbiddenPairsWanted`.

The vertices are `0, …, n - 1`; the edges are a simple edge list (no loops, no repeated edge in
either orientation, endpoints below `n`), as in `LongestPathWithForbiddenPairsWanted`, and the
pairs are a list of pairs of vertices below `n`. A simple path from `s` to `f` is a list of
distinct vertices that starts at `s`, ends at `f`, and joins consecutive vertices by an edge
(`List.IsChain`); for `s = f` the one-vertex path `[s]` counts. Its number of edges is its
length minus one. "At most one vertex from each pair" means, as in
`PathWithForbiddenPairsWanted`, that a path containing both `aⱼ` and `bⱼ` has `aⱼ = bⱼ`.
`WellFormed` requires `0 < K` (the source's "positive integer K").

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, edge list, the list of pairs `C`, the initial vertex `s`, the
final vertex `f`, and the bound `K`. -/
abbrev ShortestPathWithForbiddenPairsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: the edge list is a simple graph on `0, …, n - 1`, the
pairs, `s` and `f` use vertices below `n`, and `0 < K`. -/
def WellFormed (i : ShortestPathWithForbiddenPairsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ c ∈ i.2.2.1, c.1 < i.1 ∧ c.2 < i.1) ∧ i.2.2.2.1 < i.1 ∧ i.2.2.2.2.1 < i.1 ∧
      0 < i.2.2.2.2.2

/-- A simple path from `s` to `f` with at most `K` edges containing at most one vertex from
each pair. -/
def ShortestPathWithForbiddenPairsFeasible (i : ShortestPathWithForbiddenPairsInstance) :
    Prop :=
  ∃ p : List ℕ, p.head? = some i.2.2.2.1 ∧ p.getLast? = some i.2.2.2.2.1 ∧ p.Nodup ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1 ∨ (v, u) ∈ i.2.1) ∧
      (∀ c ∈ i.2.2.1, c.1 ∈ p → c.2 ∈ p → c.1 = c.2) ∧ p.length ≤ i.2.2.2.2.2 + 1

open Classical in
/-- SHORTEST PATH WITH FORBIDDEN PAIRS as a decision problem over bitstrings. -/
noncomputable def shortestPathWithForbiddenPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestPathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ ShortestPathWithForbiddenPairsFeasible i)
  | none => false

/-- **SHORTEST PATH WITH FORBIDDEN PAIRS is NP-complete.** Source: Crescenzi and Kann, SHORTEST
PATH WITH FORBIDDEN PAIRS; Kann (1994); Gabow, Maheshwari and Osterweil (1976); Garey and Johnson
(1979), [GT54]. -/
public theorem_wanted shortestPathWithForbiddenPairs_npComplete :
    shortestPathWithForbiddenPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestPathWithForbiddenPairsDec

end MetaMathlibExt.Complexity.NPComplete.ShortestPathWithForbiddenPairs
