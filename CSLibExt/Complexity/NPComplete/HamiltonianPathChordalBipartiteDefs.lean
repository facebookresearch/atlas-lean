/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on chordal bipartite graphs: definitions

Source:
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4 ("The main result of this paper is the
NP-completeness of the HAMILTONIAN CIRCUIT problem for chordal bipartite graphs. ... On both
classes the complexity of the HAMILTONIAN PATH problem coincides with the complexity of
HAMILTONIAN CIRCUIT");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance (`0 < n`, a simple
graph given by an edge list) that is bipartite and has no induced cycle of length at least `6`. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsBipartite ∧
    ∀ k, 6 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)

open Classical in
/-- HAMILTONIAN PATH on chordal bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathChordalBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧
      HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathChordalBipartite
