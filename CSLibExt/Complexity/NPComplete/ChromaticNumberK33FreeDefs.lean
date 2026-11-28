/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for K₃,₃-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
remains NP-complete for `K = 3` and planar graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of
Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-Free",
column "ChrNum": "N [GJ]"), and Section 3 ("K3,3-free Graphs. These are graphs that contain no
subgraphs homeomorphic to K3,3 but may contain ones homeomorphic to K5.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Connectivity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberK33Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

/-- `G` has a subgraph homeomorphic to `K₃,₃`: distinct branch vertices `a i`, `b j`
(`i, j : Fin 3`) and paths `P i j` from `a i` to `b j`, pairwise internally disjoint, whose
interiors (`support.tail.dropLast`) avoid every branch vertex. -/
def HasK33Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b : Fin 3 → V) (P : ∀ i j, G.Walk (a i) (b j)),
    Function.Injective (Sum.elim a b) ∧ (∀ i j, (P i j).IsPath) ∧
      (∀ i j i' j', (i, j) ≠ (i', j') → SimpleGraph.InternallyDisjoint (P i j) (P i' j')) ∧
      ∀ i j k, a k ∉ (P i j).support.tail.dropLast ∧ b k ∉ (P i j).support.tail.dropLast

/-- Well-formedness of an instance: the parent's simple edge list on vertices below `n`, `K` is
positive, and the graph has no subgraph homeomorphic to `K₃,₃`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ ¬ HasK33Subdivision (Graph i)

open Classical in
/-- CHROMATIC NUMBER for `K₃,₃`-free graphs as a decision problem over bitstrings. -/
noncomputable def chromaticNumberK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberK33Free
