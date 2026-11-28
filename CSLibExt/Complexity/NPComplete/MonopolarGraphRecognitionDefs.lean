/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLAR GRAPH RECOGNITION: definitions

Source:
A. Farrugia, "Vertex-partitioning into fixed additive induced-hereditary properties is
NP-hard", Electronic Journal of Combinatorics 11 (2004), #R46, doi:10.37236/1799
(arXiv:math/0306158; Theorem 2);
ISGCI (https://www.graphclasses.org/classes/gc_1272.html), class monopolar, problem
"Recognition": NP-complete, citing Farrugia.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityMonopolarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarGraphRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev MonopolarGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MonopolarGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : MonopolarGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is monopolar. -/
def MonopolarGraphRecognitionFeasible (i : MonopolarGraphRecognitionInstance) : Prop :=
  ThreeColorabilityMonopolar.IsMonopolar (Graph i)

open Classical in
/-- MONOPOLAR GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def monopolarGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonopolarGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ MonopolarGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonopolarGraphRecognition
