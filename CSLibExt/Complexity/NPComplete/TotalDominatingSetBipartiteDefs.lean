/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET on bipartite graphs: definitions

Source:
J. Pfaff, R. C. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination
and irredundance for bipartite graphs", Technical Report 428, Department of Mathematical
Sciences, Clemson University (1983) (the original proof; not available online);
M. A. Shalu and V. K. Kirubakaran, "Total domination and open packing in some subclasses of
bipartite graphs", Journal of Combinatorial Optimization 50(5) (2025), article 44,
doi:10.1007/s10878-025-01360-w (NP-completeness on a subclass of bipartite graphs; cites the
technical report).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.TotalDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`),
`0 < K ≤ |V| = n`, no isolated vertex, and the graph is bipartite. -/
def WellFormed (i : TotalDominatingSetInstance) : Prop :=
  TotalDominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (∀ v : Fin i.1, ∃ u, (Graph i).Adj v u) ∧ (Graph i).IsBipartite

open Classical in
/-- TOTAL DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def totalDominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ TotalDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetBipartite
