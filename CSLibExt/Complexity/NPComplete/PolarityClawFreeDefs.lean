/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY OF CLAW-FREE GRAPHS: definitions

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755 (recognizing polarity is NP-complete for claw-free
graphs).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityClawFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree
  (PolarityTwoKTwoCFiveFreeInstance Graph PolarityTwoKTwoCFiveFreeFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the graph is
claw-free. -/
def WellFormed (i : PolarityTwoKTwoCFiveFreeInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsClawFree

open Classical in
/-- POLARITY OF CLAW-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def polarityClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTwoKTwoCFiveFreeInstance) x with
  | some i => decide (WellFormed i ∧ PolarityTwoKTwoCFiveFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolarityClawFree
