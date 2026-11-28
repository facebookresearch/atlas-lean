/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUBICAL GRAPH RECOGNITION: definitions

Source:
F. Afrati, C. H. Papadimitriou and G. Papageorgiou, "The complexity of cubical graphs",
Information and Control 66 (1985), 53-60, doi:10.1016/S0019-9958(85)80012-7.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicalGraphRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev CubicalGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CubicalGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CubicalGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph is cubical: it is contained in the hypercube `Q_d` for some dimension `d`. -/
def CubicalGraphRecognitionFeasible (i : CubicalGraphRecognitionInstance) : Prop :=
  ∃ d : ℕ, (Graph i).IsContained (SimpleGraph.hypercubeGraph d)

open Classical in
/-- CUBICAL GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def cubicalGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CubicalGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ CubicalGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CubicalGraphRecognition
