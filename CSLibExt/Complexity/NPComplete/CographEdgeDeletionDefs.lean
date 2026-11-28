/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COGRAPH EDGE DELETION: definitions

Source:
E. S. El-Mallah and C. J. Colbourn, "The complexity of some edge deletion problems", IEEE
Transactions on Circuits and Systems 35 (1988), 354-362, doi:10.1109/31.1748;
A. Natanzon, R. Shamir and R. Sharan, "Complexity classification of some edge modification
problems", Discrete Applied Mathematics 113 (2001), 109-128,
doi:10.1016/S0166-218X(00)00391-7.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CographEdgeDeletion

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev CographEdgeDeletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CographEdgeDeletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CographEdgeDeletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Deleting at most `K` edges of `G` leaves a graph with no induced `P₄`. -/
def CographEdgeDeletionFeasible (i : CographEdgeDeletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧
    ((Graph i).edgeSet \ H.edgeSet).ncard ≤ i.2.2 ∧
      ¬ (SimpleGraph.pathGraph 4).IsIndContained H

open Classical in
/-- COGRAPH EDGE DELETION as a decision problem over bitstrings. -/
noncomputable def cographEdgeDeletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CographEdgeDeletionInstance) x with
  | some i => decide (WellFormed i ∧ CographEdgeDeletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CographEdgeDeletion
