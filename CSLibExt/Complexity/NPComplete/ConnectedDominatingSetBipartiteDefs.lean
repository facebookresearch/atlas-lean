/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET on bipartite graphs: definitions

Source:
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3 (connected domination is NP-complete for chordal bipartite
graphs, as recorded by T. Liu, Z. Lu and K. Xu, "Tractable connected domination for restricted
bipartite graphs", Journal of Combinatorial Optimization 29 (2015), 247-256,
doi:10.1007/s10878-014-9729-x);
J. Pfaff, R. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination and
irredundance for bipartite graphs", Technical Report 428, Department of Mathematical Sciences,
Clemson University (1983) (the bipartite case; the report was not available);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), CONNECTED DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.ConnectedDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
  (ConnectedDominatingSetInstance Graph ConnectedDominatingSetFeasible)

/-- Well-formedness of an instance: a well-formed CONNECTED DOMINATING SET instance (a simple
edge list on `Fin n`) whose graph is bipartite, with `0 < K ≤ n`. -/
def WellFormed (i : ConnectedDominatingSetInstance) : Prop :=
  ConnectedDominatingSet.WellFormed i ∧ (Graph i).IsBipartite ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CONNECTED DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def connectedDominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetBipartite
