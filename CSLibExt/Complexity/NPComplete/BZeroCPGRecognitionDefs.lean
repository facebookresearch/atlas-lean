/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B0-CPG GRAPH RECOGNITION: definitions

Source:
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), Lecture Notes in Computer Science 11282 (2018), 317-330,
doi:10.1007/978-3-030-04414-5_22, Theorem 2 (arXiv:1803.03468).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityB0CPGDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BZeroCPGRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev BZeroCPGRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BZeroCPGRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BZeroCPGRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is a `B_0`-CPG graph. -/
def BZeroCPGRecognitionFeasible (i : BZeroCPGRecognitionInstance) : Prop :=
  ThreeColorabilityB0CPG.IsB0CPG (Graph i)

open Classical in
/-- B0-CPG GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def bZeroCPGRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BZeroCPGRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ BZeroCPGRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BZeroCPGRecognition
