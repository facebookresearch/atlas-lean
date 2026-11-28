/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on cubic planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 199, problem [GT39] HAMILTONIAN PATH,
comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (1) of [GT37] is "if `G` is planar, cubic, 3-connected, and has no face with fewer
than 5 edges" [Garey, Johnson and Tarjan, 1976a];
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1102` (cubic ∩
planar), problem Hamiltonian path: NP-complete (Garey, Johnson and Tarjan 1976; Picouleau 1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is
cubic (every vertex has degree exactly `3`) and planar. -/
def CubicPlanarWellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsPlanar

open Classical in
/-- HAMILTONIAN PATH on cubic planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (CubicPlanarWellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanar
