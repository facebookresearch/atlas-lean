/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLAR GRAPH RECOGNITION: definitions

Source:
Zh. A. Chernyak and A. A. Chernyak, "About recognizing (α, β) classes of polar graphs",
Discrete Mathematics 62 (1986), 133-138, doi:10.1016/0012-365X(86)90113-5;
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032;
ISGCI (https://www.graphclasses.org/classes/gc_314.html), problem "Recognition" on polar
graphs: NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PolarityTriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarGraphRecognition

open MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree (IsPolar)

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PolarGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PolarGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PolarGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is polar. -/
def PolarGraphRecognitionFeasible (i : PolarGraphRecognitionInstance) : Prop :=
  IsPolar (Graph i)

open Classical in
/-- POLAR GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def polarGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PolarGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolarGraphRecognition
