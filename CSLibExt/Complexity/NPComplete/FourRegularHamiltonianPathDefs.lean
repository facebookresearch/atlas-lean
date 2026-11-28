/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN 4-REGULAR GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical Computer
Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6;
ISGCI (Information System on Graph Classes and their Inclusions), class 4-regular (gc_1101),
problem Hamiltonian path: NP-complete [Picouleau 1994].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FourRegularHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph HamiltonianPathUndirectedFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is
4-regular. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsRegularOfDegree 4

open Classical in
/-- HAMILTONIAN PATH IN 4-REGULAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def fourRegularHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FourRegularHamiltonianPath
