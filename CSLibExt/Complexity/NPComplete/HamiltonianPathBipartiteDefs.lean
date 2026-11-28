/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH for bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, p. 199
(comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (2) of [GT37] is "if G is bipartite [Krishnamoorthy, 1975]");
M. S. Krishnamoorthy, "An NP-hard problem in bipartite graphs", SIGACT News 7 (1975), 26,
doi:10.1145/990518.990521;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBipartite

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance (`0 < n`, simple
edge list) whose graph is bipartite (`SimpleGraph.IsBipartite`). -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- HAMILTONIAN PATH for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBipartite
