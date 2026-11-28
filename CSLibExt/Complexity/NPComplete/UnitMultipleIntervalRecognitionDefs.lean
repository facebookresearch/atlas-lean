/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT d-INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2: definitions

Source:
V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple interval
graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011, Corollary 21 (arXiv:2309.11908; ISAAC 2023).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev UnitMultipleIntervalRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : UnitMultipleIntervalRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : UnitMultipleIntervalRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a unit `d`-interval graph: each vertex `v` is assigned `d` pairwise disjoint closed
unit intervals `[l v j, l v j + 1]` (`j : Fin d`), and two distinct vertices are adjacent in `H`
exactly when the unions of their intervals intersect. -/
def IsUnitMultipleIntervalGraph (d : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l : Fin n → Fin d → ℝ,
    (∀ v j j', j ≠ j' →
      Disjoint (Set.Icc (l v j) (l v j + 1)) (Set.Icc (l v j') (l v j' + 1))) ∧
    ∀ u v, u ≠ v →
      (H.Adj u v ↔
        ((⋃ j, Set.Icc (l u j) (l u j + 1)) ∩ (⋃ j, Set.Icc (l v j) (l v j + 1))).Nonempty)

/-- The graph of the instance is a unit `d`-interval graph. -/
def UnitMultipleIntervalRecognitionFeasible (d : ℕ)
    (i : UnitMultipleIntervalRecognitionInstance) : Prop :=
  IsUnitMultipleIntervalGraph d (Graph i)

open Classical in
/-- UNIT d-INTERVAL GRAPH RECOGNITION, for the fixed `d`, as a decision problem over
bitstrings. -/
noncomputable def unitMultipleIntervalRecognitionDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultipleIntervalRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultipleIntervalRecognitionFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition
