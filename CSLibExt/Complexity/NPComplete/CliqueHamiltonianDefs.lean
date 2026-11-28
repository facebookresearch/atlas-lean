/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on Hamiltonian graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 6.2 and Lemma 6.3;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "hamiltonian"
(gc_1092), problem Clique: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueHamiltonian

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is Hamiltonian (`n ≥ 3` and a Hamiltonian cycle exists). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ 3 ≤ i.1 ∧ (Graph i).IsHamiltonian

/-- The graph has a clique of size `K` or more. -/
def CliqueHamiltonianFeasible (i : GraphColoringInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def cliqueHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CliqueHamiltonianFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueHamiltonian
