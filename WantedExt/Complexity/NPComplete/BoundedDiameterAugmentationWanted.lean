/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER AUGMENTATION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM BOUNDED DIAMETER AUGMENTATION;
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "On the minimum-cardinality-bounded-diameter and
the bounded-cardinality-minimum-diameter edge addition problems", Operations Research Letters
11 (1992), 303-308, doi:10.1016/0167-6377(92)90007-P.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation

/-!
# BOUNDED DIAMETER AUGMENTATION is NP-complete

INSTANCE: a graph `G = (V, E)`, a positive integer `D < |V|`, and a positive integer `K`.
QUESTION: is there an augmenting set `E'` for `G`, a set of unordered pairs of vertices from `V`,
such that `G' = (V, E ∪ E')` has diameter at most `D` (the maximum distance of any pair of
vertices is at most `D`) and `|E'| ≤ K`?

This is the decision version, with bound `K`, of Crescenzi and Kann's MINIMUM BOUNDED
DIAMETER AUGMENTATION, the minimum-cardinality-bounded-diameter (MCBD) edge addition problem of
Li, McCormick and Simchi-Levi (1992): "Given a graph `G = (V, E)`, positive integer `D < |V|`
[…], find a superset of edges `E′ ⊇ E` such that the graph `G′ = (V, E′)` has diameter no greater
than `D` and the total number of the new edges is minimized." They prove MCBD NP-hard even
when `D = 2`. It is in NP: the added edges, at most `|V|²` of them, are a certificate, and the
diameter is computed by breadth-first search.

The graph is given by its number of vertices `n = |V|`, written in unary as the length of a
list `[true, …, true]` (as the bound in `BoundedStripsPlanningWanted`), and an edge list on
`Fin n`. A graph is given with its vertex set, so the input length is at least `|V|`; a binary
`n` would make the problem succinct, since an edgeless graph on `2^m` vertices would take `O(m)`
bits while every augmenting set reaching finite diameter has at least `2^m - 1` pairs.

The augmenting set is a `SimpleGraph (Fin n)` `H`, `G'` is `G ⊔ H`, and `|E'|` is
`H.edgeSet.ncard`. Pairs `{v, v}` cannot shorten a distance and pairs already in `E` change
nothing in `G ⊔ H`, so dropping them keeps a solution; counting all edges of `H` therefore gives
the same answer as counting only the new ones. The diameter is
Mathlib's `SimpleGraph.ediam`, the supremum of the distances `SimpleGraph.edist`, which is `⊤`
for a disconnected graph. `K` is a positive integer, following the Garey-Johnson convention for
decision versions; for `K = 0` the question is whether `G` itself has diameter at most `D`,
which breadth-first search decides.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` in unary (a list of length `n`; vertices `0, …, n - 1`),
the edge list, the diameter bound `D`, and the bound `K` on the number of added edges. -/
abbrev BoundedDiameterAugmentationInstance := List Bool × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`, `n` the length of the unary list. -/
def Graph (i : BoundedDiameterAugmentationInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1

/-- Well-formedness of an instance: `n` is written in unary as `[true, …, true]`, the edge list
describes a simple graph (no duplicate edges in either orientation, no self-loops, endpoints in
range), `0 < D < |V|`, and `K` is positive. -/
def WellFormed (i : BoundedDiameterAugmentationInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ i.2.2.1 < i.1.length ∧ 0 < i.2.2.2

/-- Some set `H` of at most `K` vertex pairs makes the diameter of `G ⊔ H` at most `D`. -/
def BoundedDiameterAugmentationFeasible (i : BoundedDiameterAugmentationInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1.length), H.edgeSet.ncard ≤ i.2.2.2 ∧
    (Graph i ⊔ H).ediam ≤ (i.2.2.1 : ℕ∞)

open Classical in
/-- BOUNDED DIAMETER AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def boundedDiameterAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ BoundedDiameterAugmentationFeasible i)
  | none => false

/-- **BOUNDED DIAMETER AUGMENTATION is NP-complete.** Source: Crescenzi and Kann (2000), MINIMUM
BOUNDED DIAMETER AUGMENTATION; Li, McCormick and Simchi-Levi (1992). -/
public theorem_wanted boundedDiameterAugmentation_npComplete :
    boundedDiameterAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedDiameterAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation
