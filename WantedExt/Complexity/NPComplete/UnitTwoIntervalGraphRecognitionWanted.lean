/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT 2-INTERVAL GRAPH RECOGNITION is NP-complete

Source:
V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple interval
graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011 (conference version: ISAAC 2023, arXiv:2309.11908), Theorem 17
("Unit 2-Interval Recognition is NP-complete, even for graphs of degree at most 7");
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_877`
(unit 2-interval), problem Recognition: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IntervalNumberAtMostKWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition

open IntervalNumberAtMostK (IntervalNumberAtMostKInstance Graph WellFormed)

/-!
# UNIT 2-INTERVAL GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a unit 2-interval graph, that is, can each vertex be associated with the union
of two disjoint closed real intervals of length `1` so that two distinct vertices are adjacent
exactly when their unions intersect?

Ardévol Martínez, Rizzi, Sikora and Vialette, Section 2: "An interval is a set of real numbers of
the form `[a, b] := {x ∈ ℝ | a ⩽ x ⩽ b}`. A `d`-interval is the union of `d` disjoint intervals.
A `d`-interval is balanced if all its `d` intervals have the same length, and unit when this
common length is 1." A family of `d`-intervals represents the graph whose vertices are its
members, "two `d`-intervals [being] adjacent if and only if their intersection is not empty";
"each vertex is associated with a `d`-interval" (Section 1). They note that, unlike for
unrestricted lengths, requiring the intervals of a `d`-interval to be disjoint changes the class
of unit `d`-interval graphs, and they study the disjoint case. Their Theorem 17 states that
UNIT 2-INTERVAL RECOGNITION is NP-complete ("the problem is clearly in NP").

`IsUnitTwoIntervalGraph H` assigns each vertex `v` the left endpoints `l v 0`, `l v 1` of two
closed unit intervals `[l v j, l v j + 1]` with empty intersection, and two distinct vertices are
adjacent exactly when the unions of their intervals intersect, the shape of
`IntervalNumberAtMostK.IsMultipleIntervalGraph` with the unit lengths and the disjointness
added. The instance (vertex count and edge list), the graph (`Cslib.Complexity.Karp.edgeGraph`
on `Fin n`) and `WellFormed` (a simple edge list) are those of
`WantedExt.Complexity.NPComplete.IntervalNumberAtMostKWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **UNIT 2-INTERVAL GRAPH RECOGNITION is NP-complete.** Source: Ardévol Martínez, Rizzi,
Sikora and Vialette (2025), Theorem 17. -/
public theorem_wanted unitTwoIntervalGraphRecognition_npComplete :
    unitTwoIntervalGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitTwoIntervalGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition
