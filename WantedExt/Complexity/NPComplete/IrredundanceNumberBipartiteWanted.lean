/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IRREDUNDANCE NUMBER on bipartite graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5 (1984),
147-160, doi:10.1016/0196-6774(84)90045-2, Section 2 (DOMINATING SET update: "The results for
bipartite and split graphs can be extended to CONNECTED DOMINATING SET, TOTAL DOMINATING SET
[...], and IRREDUNDANCE NUMBER [45,62]");
J. Pfaff, R. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination and
irredundance for bipartite graphs", Technical Report 428, Department of Mathematical Sciences,
Clemson University (1983) (the bipartite case; the report was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IrredundanceNumberBipartite

open GraphColoring (GraphColoringInstance Graph)

/-!
# IRREDUNDANCE NUMBER on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is the irredundance number of `G` at most `K`, i.e. is there a maximal irredundant set
`V' ⊆ V` with `|V'| ≤ K`?

Johnson's column defines the irredundance number as "the minimum size of a maximal irredundant
set, where `v ∈ V'` is redundant if it is adjacent to another member of `V'` and each of its
neighbors is either in `V'`, or adjacent to some vertex in `V' - {v}`", and reports it
NP-complete for bipartite graphs (Pfaff, Laskar and Hedetniemi); the same column reports split
graphs (Laskar and Pfaff), a separate restriction not stated here. A set is irredundant when
none of its members is redundant (`IsIrredundant`), and a maximal irredundant set is Mathlib's
`Maximal` for that predicate under inclusion. The bound `K ≤ |V|` follows the convention of
DOMINATING SET ([GT2]), since the irredundance number is at most the domination number.

The instance (vertex count `n`, simple edge list, `K`), the graph and the simple-edge-list
conditions are those of `GraphColoringWanted`, reused unchanged; bipartiteness is Mathlib's
`SimpleGraph.IsBipartite` (a proper 2-coloring), as in `ConnectedDominatingSetBipartiteWanted`.
An isolated vertex is never redundant and does not change whether other vertices are, so it
belongs to every maximal irredundant set; a certificate lists only the members that lie on
edges, and the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `v` is redundant in `S` (Johnson's wording): `v` is adjacent to another member of `S`, and
each neighbor of `v` is in `S` or adjacent to some vertex of `S - {v}`. -/
def IsRedundant {V : Type*} (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  (∃ w ∈ S, w ≠ v ∧ G.Adj v w) ∧ ∀ u, G.Adj v u → u ∈ S ∨ ∃ w ∈ S, w ≠ v ∧ G.Adj u w

/-- `S` is irredundant: none of its members is redundant in `S`. -/
def IsIrredundant {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ¬ IsRedundant G S v

/-- Well-formedness of an instance: a simple edge list on `Fin n`, a bipartite graph, and
`0 < K ≤ |V|`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (Graph i).IsBipartite ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some maximal irredundant set has at most `K` vertices. -/
def IrredundanceNumberBipartiteFeasible (i : GraphColoringInstance) : Prop :=
  ∃ S : Finset (Fin i.1), Maximal (IsIrredundant (Graph i)) S ∧ S.card ≤ i.2.2

open Classical in
/-- IRREDUNDANCE NUMBER on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def irredundanceNumberBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ IrredundanceNumberBipartiteFeasible i)
  | none => false

/-- **IRREDUNDANCE NUMBER on bipartite graphs is NP-complete.** Source: Johnson (1984),
NP-completeness column (Pfaff, Laskar, and Hedetniemi, 1983). -/
public theorem_wanted irredundanceNumberBipartite_npComplete :
    irredundanceNumberBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L irredundanceNumberBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.IrredundanceNumberBipartite
