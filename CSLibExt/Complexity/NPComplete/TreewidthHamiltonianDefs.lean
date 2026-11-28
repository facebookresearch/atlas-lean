/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH on Hamiltonian graphs: definitions

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 7.3;
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024 (the
parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "hamiltonian"
(gc_1092), problem treewidth: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthHamiltonian

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (a simple edge list on
`Fin n`) whose graph has a Hamiltonian cycle. -/
def HamiltonianWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ∃ (a : Fin i.1) (p : (Graph i).Walk a a), p.IsHamiltonianCycle

open Classical in
/-- TREEWIDTH on Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def treewidthHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (HamiltonianWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthHamiltonian
