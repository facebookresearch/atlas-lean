/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on line graphs of bipartite graphs: definitions

Source:
T.-H. Lai and S.-S. Wei, "The edge Hamiltonian path problem is NP-complete for bipartite
graphs", Information Processing Letters 46 (1993), 21-26, doi:10.1016/0020-0190(93)90191-B;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-- `G` is the line graph of a bipartite graph: isomorphic to `L(H)` for a bipartite graph `H`
on some `Fin k`. -/
def IsBipartiteLineGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is the
line graph of a bipartite graph. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ IsBipartiteLineGraph (Graph i)

open Classical in
/-- HAMILTONIAN PATH on line graphs of bipartite graphs as a decision problem over bitstrings. -/
noncomputable def bipartiteLineGraphHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianPath
