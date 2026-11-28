/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT COVER: definitions

Source:
R. Motwani and J. Naor, "On exact and approximate cut covers of graphs", Technical Note
STAN-CS-TN-94-11, Department of Computer Science, Stanford University (1994), Theorem 2.1;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
MINIMUM CUT COVER (citing Motwani and Naor);
R. Loulou, "Minimal cut cover of a graph with an application to the testing of electronic
boards", Operations Research Letters 12 (1992), 301-305, doi:10.1016/0167-6377(92)90089-L
(introduces the problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutCover

open GraphColoring (GraphColoringInstance Graph WellFormed)

/-- Some collection of at most `K` vertex subsets `V₀, ..., Vₘ₋₁` cuts every edge: for each edge
`uv`, some `Vⱼ` contains exactly one of `u` and `v`. -/
def CutCoverFeasible (i : GraphColoringInstance) : Prop :=
  ∃ m ≤ i.2.2, ∃ V : Fin m → Finset (Fin i.1), ∀ u v, (Graph i).Adj u v →
    ∃ j, (u ∈ V j ∧ v ∉ V j) ∨ (u ∉ V j ∧ v ∈ V j)

open Classical in
/-- CUT COVER as a decision problem over bitstrings. -/
noncomputable def cutCoverDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CutCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CutCover
