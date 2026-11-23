/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circle graphs for fixed K ≥ 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
W. Unger, "On the k-colouring of circle-graphs", STACS 88, Lecture Notes in Computer Science
294 (1988), 61-72, doi:10.1007/BFb0035832;
P. Bachmann, I. Rutter and P. Stumpf, "On 3-coloring circle graphs", Journal of Graph
Algorithms and Applications 28 (2024), 389-402, doi:10.7155/jgaa.v28i1.2991.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircleGraphFixedKColoring

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-!
# GRAPH K-COLORABILITY of circle graphs for fixed K ≥ 4 is NP-complete

For a fixed integer `K ≥ 4`:
INSTANCE: a circle graph `G = (V, E)`, given by a chord model (a family of chords of a circle,
one per vertex, two vertices adjacent when their chords intersect).
QUESTION: is `G` `K`-colorable, i.e., is there a function `f : V → {1, 2, ..., K}` such that
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`?

This is GRAPH K-COLORABILITY ([GT4], `GraphColoringWanted`) restricted to circle graphs, with
the number of colors `K` fixed instead of part of the instance; the version with `K` in the
instance is `GraphColoringCircleGraphWanted`. Unger (1988) proves the fixed-`K` problem
NP-complete for every `K ≥ 4`; Bachmann, Rutter and Stumpf (Section 1) record this result with
that citation, note that the problem is easy for `K ≤ 2`, and argue that the case `K = 3`
should be considered open.

The chord model and the circle graph are those of
`WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted`, also used by
`GraphColoringCircleGraphWanted`: a chord is given by its two endpoints, natural numbers
`a < b` naming points in clockwise order on the circle; the endpoints of all chords are
distinct; `DominatingSetCircleGraph.circleGraph` joins two chords when their endpoints
interleave, which for distinct endpoints is exactly when they intersect. Every circle graph has
such a model. `K`-colorability is Mathlib's `SimpleGraph.Colorable`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`; the number
of colors `K` is fixed. -/
abbrev CircleGraphFixedKColoringInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every chord has endpoints `a < b`, and all endpoints of all
chords are distinct. -/
def WellFormed (i : CircleGraphFixedKColoringInstance) : Prop :=
  (∀ c ∈ i, c.1 < c.2) ∧ (i.flatMap fun c => [c.1, c.2]).Nodup

/-- The circle graph of the chords has a proper coloring with at most `K` colors. -/
def CircleGraphFixedKColoringFeasible (K : ℕ) (i : CircleGraphFixedKColoringInstance) : Prop :=
  (circleGraph i).Colorable K

open Classical in
/-- GRAPH K-COLORABILITY of circle graphs for a fixed `K` as a decision problem over
bitstrings. -/
noncomputable def circleGraphFixedKColoringDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircleGraphFixedKColoringInstance) x with
  | some i => decide (WellFormed i ∧ CircleGraphFixedKColoringFeasible K i)
  | none => false

/-- **GRAPH K-COLORABILITY of circle graphs is NP-complete for every fixed `K ≥ 4`.** Source:
Garey and Johnson (1979), [GT4]; Unger (1988). -/
public theorem_wanted circleGraphFixedKColoring_npComplete (K : ℕ) (hK : 4 ≤ K) :
    circleGraphFixedKColoringDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (circleGraphFixedKColoringDec K)

end MetaMathlibExt.Complexity.NPComplete.CircleGraphFixedKColoring
