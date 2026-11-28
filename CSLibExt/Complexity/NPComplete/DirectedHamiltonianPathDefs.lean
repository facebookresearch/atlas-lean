/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED HAMILTONIAN PATH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, comment
("Corresponding DIRECTED HAMILTONIAN PATH problem is also NP-complete"), and Section 3.1.4,
p. 60 (undirected Hamiltonian problems transformed to their directed counterparts);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.HamPath
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleDirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath

open HamiltonianCycleDirected (HamiltonianCycleDirectedInstance WellFormed)

/-- Some list of the vertices is a directed Hamiltonian path of the digraph, between some start
vertex `s` and some end vertex `t` (`Cslib.Complexity.Karp.IsHamPath`). -/
def DirectedHamiltonianPathFeasible (i : HamiltonianCycleDirectedInstance) : Prop :=
  ∃ s t : ℕ, ∃ p : List ℕ, Cslib.Complexity.Karp.IsHamPath i.1 i.2 s t p

open Classical in
/-- DIRECTED HAMILTONIAN PATH as a decision problem over bitstrings. -/
noncomputable def directedHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleDirectedInstance) x with
  | some i => decide (WellFormed i ∧ DirectedHamiltonianPathFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath
