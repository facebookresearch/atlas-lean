/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HARMONIOUS COLORING OF TREES: definitions

Source:
K. Edwards and C. McDiarmid, "The complexity of harmonious colouring for trees", Discrete
Applied Mathematics 57 (1995), 133-144, doi:10.1016/0166-218X(94)00100-R.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HarmoniousColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HarmoniousColoringTrees



open MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring
  (HarmoniousColoringInstance Graph HarmoniousColoringFeasible)

/-- Well-formedness of an instance: well-formed for HARMONIOUS COLORING (simple edge list,
`0 < K`), and the graph is a tree. -/
def WellFormed (i : HarmoniousColoringInstance) : Prop :=
  MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring.WellFormed i ∧ (Graph i).IsTree

open Classical in
/-- HARMONIOUS COLORING OF TREES as a decision problem over bitstrings. -/
noncomputable def harmoniousColoringTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HarmoniousColoringInstance) x with
  | some i => decide (WellFormed i ∧ HarmoniousColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HarmoniousColoringTrees
