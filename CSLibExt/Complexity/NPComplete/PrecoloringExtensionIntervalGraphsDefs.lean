/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECOLORING EXTENSION ON INTERVAL GRAPHS: definitions

Source:
M. Biró, M. Hujter, and Zs. Tuza, "Precoloring extension. I. Interval graphs", Discrete
Mathematics 100(1-3) (1992), 267-279, doi:10.1016/0012-365X(92)90646-W;
D. Marx, *Graph Coloring with Local and Global Constraints*, Ph.D. thesis, Budapest University
of Technology and Economics (2004), Chapter 3 (records the result of Biró, Hujter, and Tuza).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.IntervalGraphCompletionDefs
public import CSLibExt.Complexity.NPComplete.PrecoloringExtensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecoloringExtensionIntervalGraphs

open MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension (PrecoloringExtensionInstance)
open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-- Well-formedness of an instance: a well-formed PRECOLORING EXTENSION instance whose graph is
an interval graph, with `0 < K`, every precolor at most `K`, and no edge joining two vertices
with the same precolor. -/
def WellFormed (i : PrecoloringExtensionInstance) : Prop :=
  PrecoloringExtension.WellFormed i ∧
    IsIntervalGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2.2 ∧
    (∀ v < i.1, i.2.2.1.getD v 0 ≤ i.2.2.2) ∧
    ∀ e ∈ i.2.1, i.2.2.1.getD e.1 0 ≠ 0 → i.2.2.1.getD e.1 0 ≠ i.2.2.1.getD e.2 0

open Classical in
/-- PRECOLORING EXTENSION ON INTERVAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def precoloringExtensionIntervalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PrecoloringExtensionInstance) x with
  | some i => decide (WellFormed i ∧ PrecoloringExtension.PrecoloringExtensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecoloringExtensionIntervalGraphs
