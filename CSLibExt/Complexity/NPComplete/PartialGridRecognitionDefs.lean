/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL GRID GRAPH RECOGNITION: definitions

Source:
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo, "Complexity
dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011), 2370-2379,
doi:10.1016/j.tcs.2011.01.018;
S. N. Bhatt and S. S. Cosmadakis, "The complexity of minimizing wire lengths in VLSI layouts",
Information Processing Letters 25 (1987), 263-267, doi:10.1016/0020-0190(87)90173-6;
ISGCI (https://www.graphclasses.org/classes/gc_440.html), problem "Recognition" on partial grid
graphs: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialGridRecognition

open UnitLengthTreeGridEmbedding (UnitLengthTreeGridEmbeddingInstance Graph
  UnitLengthTreeGridEmbeddingFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range); the graph need not be
a tree. -/
def WellFormed (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- PARTIAL GRID GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def partialGridRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitLengthTreeGridEmbeddingInstance) x with
  | some i => decide (WellFormed i ∧ UnitLengthTreeGridEmbeddingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialGridRecognition
