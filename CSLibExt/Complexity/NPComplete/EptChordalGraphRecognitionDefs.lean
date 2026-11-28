/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF EPT ∩ CHORDAL GRAPHS: definitions

Source:
M. C. Golumbic and R. E. Jamison, "Edge and vertex intersection of paths in a tree", Discrete
Mathematics 55 (1985), 151-159, doi:10.1016/0012-365X(85)90043-3, Theorem 3 ("It is an
NP-complete problem to decide whether a path graph is an EPT graph");
M. M. Sysło, "Triangulated edge intersection graphs of paths in a tree", Discrete Mathematics 55
(1985), 217-220, doi:10.1016/0012-365X(85)90050-0 (the reference ISGCI gives for this
recognition problem, class `gc_127`).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CSLibExt.Complexity.NPComplete.EptGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EptChordalGraphRecognition

open EptGraphRecognition
  (EptGraphRecognitionInstance Graph WellFormed EptGraphRecognitionFeasible)

/-- The graph of the instance is in `EPT ∩ chordal`: it has no induced cycle of length at least
`4`, and it is an EPT graph (`EptGraphRecognitionFeasible`). -/
def EptChordalGraphRecognitionFeasible (i : EptGraphRecognitionInstance) : Prop :=
  (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)) ∧
    EptGraphRecognitionFeasible i

open Classical in
/-- RECOGNITION OF EPT ∩ CHORDAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def eptChordalGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EptGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ EptChordalGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EptChordalGraphRecognition
