/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on cubic graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 199, problem [GT39] HAMILTONIAN PATH,
comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (1) of [GT37] is "if `G` is planar, cubic, 3-connected, and has no face with fewer
than 5 edges" [Garey, Johnson and Tarjan, 1976a];
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1100` (cubic),
problem Hamiltonian path: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubic

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is
cubic (every vertex has degree exactly `3`). -/
def CubicWellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- HAMILTONIAN PATH on cubic graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (CubicWellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubic
