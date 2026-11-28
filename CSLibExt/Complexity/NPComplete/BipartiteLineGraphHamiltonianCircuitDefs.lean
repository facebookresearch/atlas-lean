/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on line graphs of bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT
(comment (1): NP-complete for cubic graphs, from M. R. Garey, D. S. Johnson and R. E. Tarjan,
"The planar Hamiltonian circuit problem is NP-complete", SIAM Journal on Computing 5 (1976),
704-714, doi:10.1137/0205049);
T.-H. Lai and S.-S. Wei, "The edge Hamiltonian path problem is NP-complete for bipartite
graphs", Information Processing Letters 46 (1993), 21-26, doi:10.1016/0020-0190(93)90191-B.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- `G` is the line graph of a bipartite graph: isomorphic to `L(H)` for a bipartite graph `H`
on some `Fin k`. -/
def IsBipartiteLineGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
the line graph of a bipartite graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ IsBipartiteLineGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on line graphs of bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def bipartiteLineGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianCircuit
