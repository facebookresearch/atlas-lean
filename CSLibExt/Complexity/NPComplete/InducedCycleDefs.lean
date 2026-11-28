/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED CYCLE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH, comment ("The
same result holds for the variant in which 'simple path' is replaced by 'simple cycle'"),
attributed to M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of the
10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CSLibExt.Complexity.NPComplete.InducedPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedCycle

open MetaMathlibExt.Complexity.NPComplete.InducedPath (InducedPathInstance)

/-- Some set of `m ≥ K` vertices, `m ≥ 3`, induces a simple cycle on `m` vertices: the cycle
graph on `m` vertices is an induced subgraph of the instance graph. -/
def InducedCycleFeasible (i : InducedPathInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ 3 ≤ m ∧ (SimpleGraph.cycleGraph m).IsIndContained (InducedPath.Graph i)

open Classical in
/-- INDUCED CYCLE as a decision problem over bitstrings. -/
noncomputable def inducedCycleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedPathInstance) x with
  | some i => decide (InducedPath.WellFormed i ∧ InducedCycleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InducedCycle
