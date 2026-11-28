/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on 2-connected cubic planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 199, problem [GT39] HAMILTONIAN PATH,
comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (1) of [GT37] is "if `G` is planar, cubic, 3-connected, and has no face with fewer
than 5 edges" [Garey, Johnson and Tarjan, 1976a];
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"2-connected ∩ cubic ∩ planar" (gc_1183), problem Hamiltonian path: NP-complete.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianPathCubicPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanarBiconnected

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed instance of HAMILTONIAN PATH on cubic planar
graphs whose graph is also 2-connected. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathCubicPlanar.CubicPlanarWellFormed i ∧ (Graph i).IsVertexConnected 2

open Classical in
/-- HAMILTONIAN PATH on 2-connected cubic planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicPlanarBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanarBiconnected
