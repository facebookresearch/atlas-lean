/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EFFICIENT EDGE DOMINATION: definitions

Source:
D. L. Grinstead, P. J. Slater, N. A. Sherwani and N. D. Holmes, "Efficient edge domination
problems in graphs", Information Processing Letters 48 (1993), 221-228,
doi:10.1016/0020-0190(93)90084-M.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EfficientEdgeDomination

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev EfficientEdgeDominationInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EfficientEdgeDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : EfficientEdgeDominationInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- Some set `D` of edges dominates every edge exactly once: for each edge `e` there is exactly
one `d ∈ D` with `d = e` or `d` sharing an endpoint with `e`. -/
def EfficientEdgeDominationFeasible (i : EfficientEdgeDominationInstance) : Prop :=
  ∃ D : Set (Graph i).edgeSet,
    ∀ e : (Graph i).edgeSet, ∃! d, d ∈ D ∧ (d = e ∨ (Graph i).lineGraph.Adj d e)

open Classical in
/-- EFFICIENT EDGE DOMINATION as a decision problem over bitstrings. -/
noncomputable def efficientEdgeDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EfficientEdgeDominationInstance) x with
  | some i => decide (WellFormed i ∧ EfficientEdgeDominationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EfficientEdgeDomination
