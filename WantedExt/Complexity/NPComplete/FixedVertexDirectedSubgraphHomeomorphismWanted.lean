/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete for every fixed pattern whose arcs
share neither a common tail nor a common head

Source:
S. Fortune, J. Hopcroft and J. Wyllie, "The directed subgraph homeomorphism problem",
Theoretical Computer Science 10 (1980), 111-121, doi:10.1016/0304-3975(80)90009-2;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 2 (1981), 393-405,
doi:10.1016/0196-6774(81)90037-7, entry [2] SUBGRAPH HOMEOMORPHISM (FOR A FIXED GRAPH H).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism

open MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths (IsDirectedPath)

/-!
# FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete

Fix a directed pattern graph `H = (V_H, A_H)` with vertices `0, ..., k - 1` and arc list `A_H`
(no repeated arcs, no loops).

INSTANCE: a directed graph `G = (V, A)` and an injective map `m : V_H → V` prescribing the image of
each pattern vertex.
QUESTION: does `G` contain a subgraph homeomorphic to `H` with the prescribed branch vertices,
i.e., for each arc `(u, v)` of `H` a directed path in `G` from `m u` to `m v`, such that no path
passes through a prescribed vertex `m w` other than its two ends, and two different paths share
no vertex other than prescribed ones (the paths are internally vertex-disjoint)?

Johnson's column records the classification of Fortune, Hopcroft and Wyllie: the problem is
polynomial-time solvable if all arcs of `H` share a common tail, or all share a common head; for
all other fixed `H` it is NP-complete. The theorem below states the NP-complete half for every
fixed pattern without repeated arcs or loops: one decision problem per pattern `(k, A_H)`, and
the hypotheses say that no `r` is the tail of every arc and no `r` is the head of every arc (with
`r : ℕ`, so the empty pattern counts as a star and is excluded). The case where `H` is two
disjoint arcs is `DirectedTwoDisjointConnectingPathsWanted`, whose directed-path predicate
`IsDirectedPath` (distinct vertices, first `s`, last `t`, an arc from each vertex to the next) is
reused here.

The vertices of `G` are `0, ..., n - 1`, its arcs a list of ordered pairs without repetitions or
loops (as in `DirectedTwoDisjointConnectingPathsWanted`), and `m` is the list
`[m 0, ..., m (k - 1)]` of pairwise distinct vertices. Path `j` realizes the `j`-th arc of `A_H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The fixed pattern `H`: `k` vertices `0, ..., k - 1` and the arc list `A_H` has no repeated
arcs, no loops, and endpoints among the vertices. -/
def PatternWellFormed (k : ℕ) (AH : List (ℕ × ℕ)) : Prop :=
  AH.Nodup ∧ ∀ a ∈ AH, a.1 < k ∧ a.2 < k ∧ a.1 ≠ a.2

/-- An instance: vertex count `n` of `G` (vertices `0, ..., n - 1`), arc list of `G`, and the
prescribed images `[m 0, ..., m (k - 1)]` of the pattern vertices. The raw type is any natural
`n`, any list of natural pairs and an arbitrary list of natural image labels: repeated, loop and
out-of-range arcs, and image lists of any length, with repeated labels or labels at least `n`,
are representable; `WellFormed k` asks for distinct loopless arcs between vertices below `n` and
for exactly `k` pairwise distinct images below `n`. -/
abbrev FixedVertexDirectedSubgraphHomeomorphismInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- Well-formedness of an instance for a pattern with `k` vertices: the arcs of `G` are distinct,
loopless and between vertices, and `m` lists `k` pairwise distinct vertices (`m` is injective). -/
def WellFormed (k : ℕ) (i : FixedVertexDirectedSubgraphHomeomorphismInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    i.2.2.length = k ∧ i.2.2.Nodup ∧ ∀ v ∈ i.2.2, v < i.1

/-- For the `j`-th arc `(u, v)` of `AH`, the `j`-th path is a directed path from `m u` to `m v`,
every prescribed vertex on it is one of its two ends, and two paths at different positions share
only prescribed vertices. When the pattern is well formed (`PatternWellFormed k AH`) and the
instance is well formed for `k`, this says that `G` contains a subdivision of the pattern with arc
list `AH` and branch vertices `m`. On other input it can hold without such a subdivision: a
one-vertex path, which uses no arc, serves an arc of `AH` whose two ends resolve to the same label
(for instance a loop of `AH`, two indices past the end of the image list, or two indices with the
same image), and a single one-arc path may serve two arcs whose ends resolve to the same pair of
labels, such as the two copies of a repeated arc of `AH`. A path is a nonempty list of distinct
natural labels in which each consecutive pair is an entry of the arc list of `G`
(`IsDirectedPath`). The vertex count `n` is not read, so labels are not checked against it here
(under `WellFormed` every arc has both ends below `n`). The image `m u` is entry `u` of the image
list, read as `0` past its end. -/
def FixedVertexDirectedSubgraphHomeomorphismFeasible (AH : List (ℕ × ℕ))
    (i : FixedVertexDirectedSubgraphHomeomorphismInstance) : Prop :=
  ∃ paths : List (List ℕ),
    List.Forall₂ (fun a p => IsDirectedPath i.2.1 (i.2.2.getD a.1 0) (i.2.2.getD a.2 0) p ∧
      ∀ x ∈ p, x ∈ i.2.2 → x = i.2.2.getD a.1 0 ∨ x = i.2.2.getD a.2 0) AH paths ∧
    paths.Pairwise fun p q => ∀ x ∈ p, x ∈ q → x ∈ i.2.2

open Classical in
/-- FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM for the pattern `(k, AH)`, as a decision problem
over bitstrings. It is defined for any natural `k` and any arc list `AH`: the pattern is not
validated here (`PatternWellFormed` is a hypothesis of the theorem below, not part of the
problem), and a bitstring is accepted when it decodes to an instance that is well formed for `k`
and feasible for `AH`. -/
noncomputable def fixedVertexDirectedSubgraphHomeomorphismDec (k : ℕ) (AH : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedVertexDirectedSubgraphHomeomorphismInstance) x with
  | some i => decide (WellFormed k i ∧ FixedVertexDirectedSubgraphHomeomorphismFeasible AH i)
  | none => false

/-- **FIXED-VERTEX DIRECTED SUBGRAPH HOMEOMORPHISM is NP-complete** for every fixed pattern
without repeated arcs or loops in which no vertex is the tail of every arc and no vertex is the
head of every arc. Source: Fortune, Hopcroft and Wyllie (1980); Johnson (1981). -/
public theorem_wanted fixedVertexDirectedSubgraphHomeomorphism_npComplete
    (k : ℕ) (AH : List (ℕ × ℕ)) (hH : PatternWellFormed k AH)
    (htail : ¬ ∃ r : ℕ, ∀ a ∈ AH, a.1 = r) (hhead : ¬ ∃ r : ℕ, ∀ a ∈ AH, a.2 = r) :
    fixedVertexDirectedSubgraphHomeomorphismDec k AH ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedVertexDirectedSubgraphHomeomorphismDec k AH)

end MetaMathlibExt.Complexity.NPComplete.FixedVertexDirectedSubgraphHomeomorphism
