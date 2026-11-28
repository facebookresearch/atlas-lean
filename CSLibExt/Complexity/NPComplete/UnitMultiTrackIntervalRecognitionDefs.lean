/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2: definitions

Source:
M. Jiang, "Recognizing d-interval graphs and d-track interval graphs", Algorithmica 66 (2013),
541-563, doi:10.1007/s00453-012-9651-5;
recorded in V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple
interval graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011, Section 1 (arXiv:2309.11908).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import CSLibExt.Complexity.NPComplete.TrackIntervalGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition

open MetaMathlibExt.Complexity.NPComplete.TrackIntervalGraphRecognition
  (TrackIntervalGraphRecognitionInstance Graph WellFormed)

/-- `H` is a unit `d`-track interval graph: each vertex `v` is assigned one closed unit interval
`[l v j, l v j + 1]` on each track `j : Fin d`, and two distinct vertices are adjacent in `H`
exactly when their intervals on some track intersect. -/
def IsUnitMultiTrackIntervalGraph (d : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l : Fin n → Fin d → ℝ,
    ∀ u v, u ≠ v →
      (H.Adj u v ↔ ∃ j, (Set.Icc (l u j) (l u j + 1) ∩ Set.Icc (l v j) (l v j + 1)).Nonempty)

/-- The graph of the instance is a unit `d`-track interval graph. -/
def UnitMultiTrackIntervalRecognitionFeasible (d : ℕ)
    (i : TrackIntervalGraphRecognitionInstance) : Prop :=
  IsUnitMultiTrackIntervalGraph d (Graph i)

open Classical in
/-- UNIT d-TRACK INTERVAL GRAPH RECOGNITION, for the fixed `d`, as a decision problem over
bitstrings. -/
noncomputable def unitMultiTrackIntervalRecognitionDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TrackIntervalGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiTrackIntervalRecognitionFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition
