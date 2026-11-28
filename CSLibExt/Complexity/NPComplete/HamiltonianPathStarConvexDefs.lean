/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on star convex bipartite graphs: definitions

Source:
H. Chen, Z. Lei, T. Liu, Z. Tang, C. Wang and K. Xu, "Complexity of domination, Hamiltonicity
and treewidth for tree convex bipartite graphs", Journal of Combinatorial Optimization 32 (2016),
95-110, doi:10.1007/s10878-015-9917-3;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the unrestricted
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class star convex (gc_1151),
problem Hamiltonian path: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetStarConvexDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathStarConvex

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is star
convex bipartite. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ FeedbackVertexSetStarConvex.IsStarConvex (Graph i)

open Classical in
/-- HAMILTONIAN PATH on star convex bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathStarConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathStarConvex
