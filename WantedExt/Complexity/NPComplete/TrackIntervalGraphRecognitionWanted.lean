/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Source:
M. Jiang, "Recognizing d-interval graphs and d-track interval graphs", Algorithmica 66 (2013),
541-563, doi:10.1007/s00453-012-9651-5;
ISGCI (https://www.graphclasses.org/classes/gc_1079.html and gc_1080.html), problem
"Recognition" on 2-track and 3-track graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TrackIntervalGraphRecognition

/-!
# d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Fix an integer `d ≥ 2`.
INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a `d`-track interval graph?

Jiang (2013): "A `d`-track interval is the union of `d` disjoint intervals on `d` disjoint
parallel lines called tracks, one interval on each track." A `d`-track interval graph is the
intersection graph of a family of `d`-track intervals: two different vertices are adjacent if
and only if their `d`-track intervals intersect. Jiang proves that recognizing `d`-track
interval graphs is NP-complete for every constant `d ≥ 2`. The tracks are disjoint, so two
`d`-track intervals intersect exactly when their intervals on some common track intersect.

`IsTrackIntervalGraph d H` assigns each vertex `v` one closed interval `[l v j, r v j]`
(`l v j ≤ r v j`) on each track `j : Fin d`, and makes two distinct vertices adjacent exactly
when their intervals on some track `j` intersect. Equivalently, `H` is the edge union of `d`
interval graphs on its vertex set. Closed intervals give the same graph class as open or
half-open ones for finite graphs. The graph is given by an edge list on `Fin n` as in the
other graph statements of this directory (`Cslib.Complexity.Karp.edgeGraph`); the
`d`-interval analogue, with all intervals on one line, is
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

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev TrackIntervalGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TrackIntervalGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TrackIntervalGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `d`-track interval graph: each vertex `v` is assigned one closed real interval
`[l v j, r v j]` on each track `j : Fin d`, and two distinct vertices are adjacent in `H`
exactly when their intervals on some track intersect. -/
def IsTrackIntervalGraph (d : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l r : Fin n → Fin d → ℝ, (∀ v j, l v j ≤ r v j) ∧
    ∀ u v, u ≠ v →
      (H.Adj u v ↔ ∃ j, (Set.Icc (l u j) (r u j) ∩ Set.Icc (l v j) (r v j)).Nonempty)

/-- The graph of the instance is a `d`-track interval graph. -/
def TrackIntervalGraphRecognitionFeasible (d : ℕ)
    (i : TrackIntervalGraphRecognitionInstance) : Prop :=
  IsTrackIntervalGraph d (Graph i)

open Classical in
/-- d-TRACK INTERVAL GRAPH RECOGNITION, for the fixed number of tracks `d`, as a decision
problem over bitstrings. -/
noncomputable def trackIntervalGraphRecognitionDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TrackIntervalGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ TrackIntervalGraphRecognitionFeasible d i)
  | none => false

/-- **d-TRACK INTERVAL GRAPH RECOGNITION is NP-complete for every fixed `d ≥ 2`.** Source:
Jiang (2013). -/
public theorem_wanted trackIntervalGraphRecognition_npComplete (d : ℕ) (hd : 2 ≤ d) :
    trackIntervalGraphRecognitionDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (trackIntervalGraphRecognitionDec d)

end MetaMathlibExt.Complexity.NPComplete.TrackIntervalGraphRecognition
