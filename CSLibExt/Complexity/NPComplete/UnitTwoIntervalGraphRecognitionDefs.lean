/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT 2-INTERVAL GRAPH RECOGNITION: definitions

Source:
V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple interval
graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011 (conference version: ISAAC 2023, arXiv:2309.11908), Theorem 17
("Unit 2-Interval Recognition is NP-complete, even for graphs of degree at most 7");
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_877`
(unit 2-interval), problem Recognition: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntervalNumberAtMostKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition

open IntervalNumberAtMostK (IntervalNumberAtMostKInstance Graph WellFormed)

/-- `H` is a unit 2-interval graph: each vertex `v` is assigned two disjoint closed intervals
`[l v 0, l v 0 + 1]` and `[l v 1, l v 1 + 1]` of length `1`, and two distinct vertices are
adjacent in `H` exactly when the unions of their intervals intersect. -/
def IsUnitTwoIntervalGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l : Fin n → Fin 2 → ℝ,
    (∀ v, Set.Icc (l v 0) (l v 0 + 1) ∩ Set.Icc (l v 1) (l v 1 + 1) = ∅) ∧
      ∀ u v, u ≠ v →
        (H.Adj u v ↔
          ((⋃ j, Set.Icc (l u j) (l u j + 1)) ∩ (⋃ j, Set.Icc (l v j) (l v j + 1))).Nonempty)

/-- The graph of the instance is a unit 2-interval graph. -/
def UnitTwoIntervalGraphRecognitionFeasible (i : IntervalNumberAtMostKInstance) : Prop :=
  IsUnitTwoIntervalGraph (Graph i)

open Classical in
/-- UNIT 2-INTERVAL GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def unitTwoIntervalGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalNumberAtMostKInstance) x with
  | some i => decide (WellFormed i ∧ UnitTwoIntervalGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition
