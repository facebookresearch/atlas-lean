/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT d-INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Source:
V. Ardévol Martínez, R. Rizzi, F. Sikora and S. Vialette, "Recognizing unit multiple interval
graphs is hard", Discrete Applied Mathematics 360 (2025), 258-274,
doi:10.1016/j.dam.2024.09.011, Corollary 21 (arXiv:2309.11908; ISAAC 2023).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitMultipleIntervalRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition

/-!
# UNIT d-INTERVAL GRAPH RECOGNITION is NP-complete for every fixed d ≥ 2

Fix an integer `d ≥ 2`.
INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a unit `d`-interval graph?

Ardévol Martínez, Rizzi, Sikora and Vialette (Definitions): "An interval is a set of real numbers
of the form `[a, b] := {x ∈ ℝ | a ⩽ x ⩽ b}`. A `d`-interval is the union of `d` disjoint
intervals. A `d`-interval is balanced if all its `d` intervals have the same length, and unit
when this common length is 1. [...] A family `F` of `d`-intervals can be used as a representation
of the graph `Ω(F)` having the `d`-intervals of `F` as its vertex set, and where two `d`-intervals
are adjacent if and only if their intersection is not empty. A graph `G` is called a (possibly
balanced, unit) `d`-interval graph when it admits a representation `F` consisting only of
(respectively balanced, unit) `d`-intervals." Corollary 21: "Recognizing unit `d`-interval graphs
is NP-complete for every `d ⩾ 2`." They note that disjointness of the `d` intervals matters for
unit `d`-intervals and require it. The ISGCI database lists recognition of "unit 3-interval"
(gc_1083) as NP-complete, citing them.

`d` is fixed, not part of the input: the decision problem is
`unitMultipleIntervalRecognitionDec d`, and the theorem holds for every `d ≥ 2`. The graph is
given by an edge list on `Fin n`. A representation assigns to each vertex `v` and `j : Fin d` the
left endpoint `l v j` of the closed unit interval `[l v j, l v j + 1]`; the `d` intervals of a
vertex are pairwise disjoint, and two distinct vertices are adjacent exactly when the unions of
their intervals intersect (`IsUnitMultipleIntervalGraph`). The shape follows
`IntervalNumberAtMostK.IsMultipleIntervalGraph` of `WantedExt.Complexity.NPComplete.IntervalNumberAtMostKWanted`
(`t`-interval graphs with arbitrary, possibly overlapping intervals), with unit lengths and
disjointness added. The vertex count `n` is written in binary, but isolated vertices impose
nothing (their unit intervals go far from all others), so the problem reduces to the subgraph on
the at most `2|E|` non-isolated vertices, whose membership in NP is part of Corollary 21.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIT d-INTERVAL GRAPH RECOGNITION is NP-complete for every fixed `d ≥ 2`.** Source:
Ardévol Martínez, Rizzi, Sikora and Vialette (2025), Corollary 21. -/
public theorem_wanted unitMultipleIntervalRecognition_npComplete (d : ℕ) (_hd : 2 ≤ d) :
    unitMultipleIntervalRecognitionDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (unitMultipleIntervalRecognitionDec d)

end MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition
