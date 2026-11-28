/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on graphs of girth at least 9: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
M. De Biasi, answer to "Polynomial problems in graph classes defined by forbidden induced cyclic
subgraphs",
Theoretical Computer Science Stack Exchange (2014), https://cstheory.stackexchange.com/a/24882
(Theorem: "for any `k ≥ 3`, the Hamiltonian cycle problem remains NP-complete even if the graph `G`
does not contain cycles of length `≤ k`", by a gadget reduction from the planar directed case of
Papadimitriou and Vazirani); ISGCI records the result for the class `girth >= 9` (`gc_1225`),
citing this answer.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGirthNine

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph has
girth at least `9` (no cycle of length below `9`). -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ 9 ≤ (Graph i).egirth

open Classical in
/-- HAMILTONIAN CIRCUIT on graphs of girth at least 9 as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGirthNine
