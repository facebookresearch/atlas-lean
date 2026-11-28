/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH for undirected path graphs: definitions

Source:
A. A. Bertossi and M. A. Bonuccelli, "Hamiltonian circuits in interval graph generalizations",
Information Processing Letters 23(4) (1986), 195-200, doi:10.1016/0020-0190(86)90135-3;
ISGCI, Information System on Graph Classes and their Inclusions, class undirected path (gc_129,
https://www.graphclasses.org/classes/gc_129.html), problem Hamiltonian path;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance HamiltonianPathUndirectedFeasible)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, `0 < n`), and
the graph is an undirected path graph. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph (HamiltonianPathUndirected.Graph i)

open Classical in
/-- HAMILTONIAN PATH for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirectedPathGraphs
