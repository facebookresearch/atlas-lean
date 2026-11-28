/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH on locally connected graphs: definitions

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024
(NP-completeness of TREEWIDTH on all graphs, the source problem of the reduction);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "locally connected"
(gc_932, https://www.graphclasses.org/classes/gc_932.html), problem treewidth decomposition:
NP-complete, reference [1506] (a note: adding a universal vertex to a connected graph gives a
locally connected graph; "Treewidth is reduced analogously to clique (Communicated by Arne
Leitert)").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthLocallyConnected

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is locally connected (every open neighbourhood induces a connected graph). -/
def LocallyConnectedWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected

open Classical in
/-- TREEWIDTH on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def treewidthLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (LocallyConnectedWellFormed i ∧ TreewidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreewidthLocallyConnected
