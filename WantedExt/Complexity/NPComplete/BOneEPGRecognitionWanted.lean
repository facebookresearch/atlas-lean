/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B₁-EPG GRAPH RECOGNITION is NP-complete

Source:
D. Heldt, K. Knauer and T. Ueckerdt, "Edge-intersection graphs of grid paths: the
bend-number", Discrete Applied Mathematics 167 (2014), 144-162,
doi:10.1016/j.dam.2013.10.035, Section 7 (arXiv:1009.2861).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BOneEPGRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition

open BkVPGRecognition (BkVPGInstance Graph IsGridPath bends)

/-!
# B₁-EPG GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a single-bend graph (a `B₁`-EPG graph), i.e. the edge-intersection graph of
paths in the plane grid with at most one bend each: are there grid paths `P(v)`, `v ∈ V`, each
with at most one bend, such that two distinct vertices `v, w` are adjacent exactly when `P(v)`
and `P(w)` have a grid edge in common?

Heldt, Knauer and Ueckerdt (Section 2): "An EPG representation is a set of finite paths
`{P(v) | v ∈ V(G)}`, which consist of consecutive edges of the rectangular grid in the plane,
such that `{v, w} ∈ E(G)` if and only if `P(v) ∩ P(w)` contains a grid-edge", and "a bend of
`P(v)` is a point of `P(v)`, where a horizontal grid-edge of `P(v)` is followed by a vertical
grid-edge of `P(v)`"; graphs with bend-number at most `1` are the single-bend graphs. Section 7
proves SINGLE-BEND-RECOGNITION NP-complete ("It is easy to verify a single-bend representation,
so SINGLE-BEND-RECOGNITION is in NP"; Theorem 7.3, NP-hardness by a reduction from ONE-IN-THREE
3-SAT).

Grid paths and their bends are those of `BkVPGRecognitionWanted`: a path is a nonempty list of
distinct points of the grid `ℕ × ℕ`, consecutive points differing by `1` in exactly one
coordinate (`IsGridPath`), and `bends` counts the inner points where a horizontal step meets a
vertical one. The grid edges of a path are its pairs of consecutive points, and two paths share
a grid edge when such a pair occurs in both, in either order (`SharesGridEdge`). A finite
representation can be translated into `ℕ × ℕ`, and a one-point path (no grid edge) behaves
like a short segment far from all other paths, so these choices do not change the class. The
paths are not part of the input.

The instance type (vertex count and edge list), the graph (`Graph`, a simple graph on `Fin n`)
and the simple-edge-list well-formedness are also reused from `BkVPGRecognitionWanted`.
Isolated vertices do not change the answer (a short segment away from all other paths), so the
binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`B₁`-EPG GRAPH RECOGNITION is NP-complete.** Source: Heldt, Knauer and Ueckerdt (2014),
Section 7. -/
public theorem_wanted bOneEPGRecognition_npComplete :
    bOneEPGRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bOneEPGRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition
