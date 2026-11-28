/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for rooted directed path graphs: definitions

Source:
B. S. Panda and D. Pradhan, "NP-completeness of Hamiltonian cycle problem on rooted directed
path graphs", arXiv:0809.2443 (2008), problem Π₁ and Theorem 3.5;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (HAMILTONIAN CIRCUIT for directed path
graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [98]);
F. Gavril, "A recognition algorithm for the intersection graphs of directed paths in directed
trees", Discrete Mathematics 13 (1975), 237-249, doi:10.1016/0012-365X(75)90021-7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs
public import CSLibExt.Complexity.NPComplete.RootedDirectedPathGraphCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRootedDirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)
open MetaMathlibExt.Complexity.NPComplete.RootedDirectedPathGraphCompletion
  (IsRootedDirectedPathGraph)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`0 < n`, simple
edge list) whose graph is a rooted directed path graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ IsRootedDirectedPathGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT for rooted directed path graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitRootedDirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRootedDirectedPathGraphs
