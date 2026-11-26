/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-SINK EDGE INSTALLATION is NP-complete

Source:
F. S. Salman, J. Cheriyan, R. Ravi and S. Subramanian, "Approximating the single-sink
link-installation problem in network design", SIAM Journal on Optimization 11 (2001), 595-610,
doi:10.1137/S1052623497321432 (conference version: "Buy-at-bulk network design: approximating
the single-sink edge installation problem", SODA 1997, 619-628);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MINIMUM SINGLE-SINK EDGE INSTALLATION (decision version);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleSinkEdgeInstallation

/-!
# SINGLE-SINK EDGE INSTALLATION is NP-complete

INSTANCE: a graph `G = (V, E)`, a length function `l : E → ℕ`, a set of sources `S ⊆ V`, a sink
`t ∈ V`, a demand function `d : S → ℤ⁺`, a finite set of cable types, each specified by its
capacity and its cost per unit length, and a positive integer `K`.
QUESTION: is there a network of cables in the graph, consisting of an integral number of each
cable type for each edge of `G`, that routes all the demands at the sources to the sink, the
demand of each source following a single path from the source to the sink, whose total cost is
at most `K`?

This is the decision version of the compendium's MINIMUM SINGLE-SINK EDGE INSTALLATION, the
single-sink link-installation (buy-at-bulk) problem of Salman, Cheriyan, Ravi and Subramanian,
who call it NP-hard. The total cost of the network is the sum over the edges `e` of `l(e)`
times the costs per unit length of the cables installed on `e`, and the cables on `e` must
carry the demands of all sources whose path uses `e`. With a single cable type of cost `1`
per unit length and capacity at least the total demand, the least cost of a network is the least
total length of a subgraph connecting `S ∪ {t}`, so the problem contains STEINER TREE IN
GRAPHS ([ND12]).

The vertices are `0, …, n - 1`; the edges are a list of triples `(u, v, l)`, an edge `{u, v}`
of length `l`, whose endpoint pairs form a simple edge list (no loops, no repeated edge in
either orientation, endpoints below `n`); the sources are a list of pairs `(v, d)` of a vertex
`v` with demand `d > 0`, with pairwise distinct vertices; the cable types are a list of pairs
`(u, c)` of a capacity `u > 0` and a cost `c` per unit length. A path from a source to the sink
is a list of distinct vertices that starts at the source, ends at `t`, and joins consecutive
vertices by an edge (`List.IsChain`); a source at the sink takes the one-vertex path `[t]`. A
path uses the edge `{u, v}` when `u` and `v` are consecutive on it, in either order. A network
installs `x(e, c) ∈ ℕ` cables of type `c` on edge `e`; on each edge, the summed demand of the
sources whose path uses the edge is at most the installed capacity `∑_c x(e, c) · u_c`, and the
total cost is `∑_e l(e) · ∑_c x(e, c) · c_c`. `WellFormed` requires `0 < K` (the compendium's
decision versions take a positive integer `K`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, edges `(u, v, l)` with lengths, sources `(v, d)` with
demands, the sink `t`, cable types `(u, c)` (capacity, cost per unit length), and the bound
`K`. -/
abbrev SingleSinkEdgeInstallationInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The endpoint pairs of the edges of the instance. -/
def edgeEnds (i : SingleSinkEdgeInstallationInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- Well-formedness of an instance: the endpoint pairs form a simple graph on `0, …, n - 1`,
the source vertices are distinct vertices with positive demands, the sink is a vertex, every
cable type has positive capacity, and `0 < K`. -/
def WellFormed (i : SingleSinkEdgeInstallationInstance) : Prop :=
  (edgeEnds i).Nodup ∧
    (∀ e ∈ edgeEnds i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ edgeEnds i) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧ (∀ s ∈ i.2.2.1, s.1 < i.1 ∧ 0 < s.2) ∧
    i.2.2.2.1 < i.1 ∧ (∀ c ∈ i.2.2.2.2.1, 0 < c.1) ∧ 0 < i.2.2.2.2.2

/-- The vertex list `p` uses the edge `{u, v}`: `u` and `v` are consecutive on `p`, in either
order. -/
abbrev UsesEdge (p : List ℕ) (u v : ℕ) : Prop :=
  (u, v) ∈ p.zip p.tail ∨ (v, u) ∈ p.zip p.tail

/-- There are a path from each source to the sink and cable counts `x j c` (cables of type `c`
on edge `j`) such that on every edge the summed demand of the sources whose path uses it is at
most the installed capacity, and the total cost `∑_j l_j · ∑_c x j c · c_c` is at most `K`. -/
def SingleSinkEdgeInstallationFeasible (i : SingleSinkEdgeInstallationInstance) : Prop :=
  ∃ (paths : Fin i.2.2.1.length → List ℕ) (x : Fin i.2.1.length → Fin i.2.2.2.2.1.length → ℕ),
    (∀ k, (paths k).head? = some (i.2.2.1.get k).1 ∧ (paths k).getLast? = some i.2.2.2.1 ∧
      (paths k).Nodup ∧ (paths k).IsChain (fun u v => (u, v) ∈ edgeEnds i ∨ (v, u) ∈ edgeEnds i)) ∧
    (∀ j, (∑ k, if UsesEdge (paths k) (i.2.1.get j).1 (i.2.1.get j).2.1 then (i.2.2.1.get k).2
        else 0) ≤ ∑ c, x j c * (i.2.2.2.2.1.get c).1) ∧
    (∑ j, (i.2.1.get j).2.2 * ∑ c, x j c * (i.2.2.2.2.1.get c).2) ≤ i.2.2.2.2.2

open Classical in
/-- SINGLE-SINK EDGE INSTALLATION as a decision problem over bitstrings. -/
noncomputable def singleSinkEdgeInstallationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleSinkEdgeInstallationInstance) x with
  | some i => decide (WellFormed i ∧ SingleSinkEdgeInstallationFeasible i)
  | none => false

/-- **SINGLE-SINK EDGE INSTALLATION is NP-complete.** Source: Salman, Cheriyan, Ravi and
Subramanian (2001); Crescenzi and Kann, MINIMUM SINGLE-SINK EDGE INSTALLATION; Garey and Johnson
(1979), [ND12]. -/
public theorem_wanted singleSinkEdgeInstallation_npComplete :
    singleSinkEdgeInstallationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleSinkEdgeInstallationDec

end MetaMathlibExt.Complexity.NPComplete.SingleSinkEdgeInstallation
