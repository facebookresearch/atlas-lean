/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IRREDUNDANCE NUMBER on bipartite graphs: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IrredundanceNumberBipartite

open GraphColoring (GraphColoringInstance Graph)

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

end MetaMathlibExt.Complexity.NPComplete.IrredundanceNumberBipartite
