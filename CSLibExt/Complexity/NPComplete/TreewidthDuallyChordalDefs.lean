/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF DUALLY CHORDAL GRAPHS: definitions

Source:
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82 (1998), 43-77,
doi:10.1016/S0166-218X(97)00125-X (Section 9, Theorem 9.2: "The problem of computing the
treewidth of a dually chordal graph is NP-complete.");
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024
(NP-completeness of TREEWIDTH on all graphs, the source problem of the reduction).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IndependentSetDuallyChordalDefs
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthDuallyChordal

open MetaMathlibExt.Complexity.NPComplete.Treewidth
open MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal (DuallyChordal)

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is dually chordal (has a maximum neighbourhood ordering). -/
def DuallyChordalWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ DuallyChordal (Graph i)

open Classical in
/-- TREEWIDTH OF DUALLY CHORDAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (DuallyChordalWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthDuallyChordal
