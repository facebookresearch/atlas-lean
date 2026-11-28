/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THRESHOLD EDITING: definitions

Source:
P. G. Drange, M. S. Dregi, D. Lokshtanov and B. D. Sullivan, "On the threshold of
intractability", Journal of Computer and System Sciences 124 (2022), 1-25,
doi:10.1016/j.jcss.2021.09.003 (conference version: ESA 2015, LNCS 9294, 411-423).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.ThresholdNumberDefs
public import Mathlib.Data.Set.Card
public import Mathlib.Order.SymmDiff

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThresholdEditing

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev ThresholdEditingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ThresholdEditingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). Every `K` is
allowed. -/
def WellFormed (i : ThresholdEditingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Some threshold graph `H` on the same vertices differs from `G` in at most `K` edges (added
or deleted). -/
def ThresholdEditingFeasible (i : ThresholdEditingInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), ThresholdNumber.IsThresholdGraph H ∧
    (symmDiff (Graph i).edgeSet H.edgeSet).ncard ≤ i.2.2

open Classical in
/-- THRESHOLD EDITING as a decision problem over bitstrings. -/
noncomputable def thresholdEditingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThresholdEditingInstance) x with
  | some i => decide (WellFormed i ∧ ThresholdEditingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThresholdEditing
