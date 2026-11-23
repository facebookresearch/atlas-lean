/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Source:
M. Jiang, "Recognizing d-interval graphs and d-track interval graphs", Algorithmica 66 (2013),
541-563, doi:10.1007/s00453-012-9651-5;
recorded in V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple
interval graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011, Section 1 (arXiv:2309.11908).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import WantedExt.Complexity.NPComplete.TrackIntervalGraphRecognitionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition

open MetaMathlibExt.Complexity.NPComplete.TrackIntervalGraphRecognition
  (TrackIntervalGraphRecognitionInstance Graph WellFormed)

/-!
# UNIT d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Fix an integer `d ≥ 2`.
INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a unit `d`-track interval graph?

A `d`-track interval is "the union of `d` disjoint intervals in `d` disjoint parallel lines called
tracks, one interval on each track"; a `d`-track interval graph is the intersection graph of a
family of `d`-track intervals, and it is a unit `d`-track interval graph when all intervals of the
representation have unit length (Jiang; the ISGCI class "unit 3-track" (gc_1081): "a 3-track
graph with an intersection model consisting of unit length intervals"). Ardévol Martínez, Rizzi,
Sikora and Vialette (Section 1) record that Gyárfás and West proved recognition of `d`-track
interval graphs NP-hard for `d = 2` and conjectured it for `d ⩾ 3`, and that "This conjecture was
proven way later [...] by Jiang, who also showed that recognition remains hard for unit `d`-track
interval graphs for any `d ⩾ 2`". The ISGCI database lists recognition of "unit 2-track"
(gc_1082) and "unit 3-track" (gc_1081) as NP-complete, citing Jiang. Membership in NP holds: a
graph is a unit `d`-track interval graph exactly when its edge set is the union of the edge sets of
`d` unit interval graphs on the same vertex set (one per track), unit interval graphs are
recognized in linear time, and, as the vertex count `n` is written in binary, isolated vertices
(whose intervals go far from all others on every track) are dropped first, leaving at most `2|E|`
vertices.

`d` is fixed, not part of the input: the decision problem is
`unitMultiTrackIntervalRecognitionDec d`, and the theorem holds for every `d ≥ 2`. The instance (a
graph given by an edge list on `Fin n`), `Graph` and `WellFormed` are those of the general
`d`-track problem, `WantedExt.Complexity.NPComplete.TrackIntervalGraphRecognitionWanted`, reused
unchanged; that module's `IsTrackIntervalGraph` allows intervals of any length, and the unit class
fixes every right endpoint to the left endpoint plus `1`. A representation assigns to each vertex `v` and track `j : Fin d`
the left endpoint `l v j` of the closed unit interval `[l v j, l v j + 1]` on track `j`; intervals
on different tracks never meet, so two distinct vertices are adjacent exactly when their intervals
on some common track intersect (`IsUnitMultiTrackIntervalGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **UNIT d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed `d ≥ 2`.** Source:
Jiang (2013); Ardévol Martínez, Rizzi, Sikora and Vialette (2025), Section 1. -/
public theorem_wanted unitMultiTrackIntervalRecognition_npComplete (d : ℕ) (_hd : 2 ≤ d) :
    unitMultiTrackIntervalRecognitionDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (unitMultiTrackIntervalRecognitionDec d)

end MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition
