/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COGRAPH EDITING: definitions

Source:
Y. Liu, J. Wang, J. Guo and J. Chen, "Complexity and parameterized algorithms for Cograph
Editing", Theoretical Computer Science 461 (2012), 45-54, doi:10.1016/j.tcs.2011.11.040.
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

namespace MetaMathlibExt.Complexity.NPComplete.CographEditing

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev CographEditingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CographEditingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CographEditingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Adding and deleting at most `K` edges of `G` gives a graph with no induced `P₄`. -/
def CographEditingFeasible (i : CographEditingInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), (symmDiff (Graph i).edgeSet H.edgeSet).ncard ≤ i.2.2 ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained H

open Classical in
/-- COGRAPH EDITING as a decision problem over bitstrings. -/
noncomputable def cographEditingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CographEditingInstance) x with
  | some i => decide (WellFormed i ∧ CographEditingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CographEditing
