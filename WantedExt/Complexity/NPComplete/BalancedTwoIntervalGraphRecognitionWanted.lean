/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED 2-INTERVAL GRAPH RECOGNITION is NP-complete

Source:
P. Gambette and S. Vialette, "On restrictions of balanced 2-interval graphs", Graph-Theoretic
Concepts in Computer Science (WG 2007), Lecture Notes in Computer Science 4769 (2007), 55-65,
doi:10.1007/978-3-540-74839-7_6 (arXiv:0704.1571; Section 1: definitions of 2-interval and
balanced 2-interval graphs; Theorem 1: "Recognizing balanced 2-interval graphs is an
NP-complete problem");
ISGCI, class "balanced 2-interval" (gc_876), problem Recognition, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedTwoIntervalGraphRecognition

/-!
# BALANCED 2-INTERVAL GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a balanced 2-interval graph?

Gambette and Vialette (Section 1): "A graph `G = (V, E)` of order `n` is a 2-interval graph if
it is the intersection graph of a set of `n` unions of two disjoint intervals on the real line,
that is each vertex corresponds to a union of two disjoint intervals `I^k = I^k_l ∪ I^k_r`, …,
and there is an edge between `I^j` and `I^k` iff `I^j ∩ I^k ≠ ∅`"; "A 2-interval graph is said
to be balanced if it has a 2-interval realization in which each 2-interval is composed of two
intervals of the same length". Theorem 1 proves recognition NP-complete.

`IsBalancedTwoIntervalRepresentation G l r`: vertex `v` gets the two closed intervals
`[l v 0, r v 0]` and `[l v 1, r v 1]` (`l v j ≤ r v j`), which are disjoint and have the same
length (`r v 0 - l v 0 = r v 1 - l v 1`), and two distinct vertices are adjacent exactly when the
unions of their intervals intersect. This is the representation of `IsMultipleIntervalGraph 2`
in `IntervalNumberAtMostKWanted` (closed intervals `Set.Icc`, indexed by `Fin 2`) with the
disjointness and equal-length conditions added; the source does not say whether intervals are
open or closed, and for finite graphs both give the same class (enlarge or shrink every interval
by the same small amount). The graph is given by an edge list on `Fin n`
(`Cslib.Complexity.Karp.edgeGraph`).

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
abbrev BalancedTwoIntervalGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BalancedTwoIntervalGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BalancedTwoIntervalGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `(l, r)` is a balanced 2-interval representation of `H`: each vertex `v` has two disjoint
closed intervals `[l v 0, r v 0]` and `[l v 1, r v 1]` of the same length, and two distinct
vertices are adjacent exactly when the unions of their intervals intersect. -/
def IsBalancedTwoIntervalRepresentation {n : ℕ} (H : SimpleGraph (Fin n))
    (l r : Fin n → Fin 2 → ℝ) : Prop :=
  (∀ v j, l v j ≤ r v j) ∧
    (∀ v, Disjoint (Set.Icc (l v 0) (r v 0)) (Set.Icc (l v 1) (r v 1))) ∧
    (∀ v, r v 0 - l v 0 = r v 1 - l v 1) ∧
    ∀ u v, u ≠ v →
      (H.Adj u v ↔
        ((⋃ j, Set.Icc (l u j) (r u j)) ∩ (⋃ j, Set.Icc (l v j) (r v j))).Nonempty)

/-- The graph of the instance is a balanced 2-interval graph. -/
def BalancedTwoIntervalGraphRecognitionFeasible
    (i : BalancedTwoIntervalGraphRecognitionInstance) : Prop :=
  ∃ l r : Fin i.1 → Fin 2 → ℝ, IsBalancedTwoIntervalRepresentation (Graph i) l r

open Classical in
/-- BALANCED 2-INTERVAL GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def balancedTwoIntervalGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedTwoIntervalGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ BalancedTwoIntervalGraphRecognitionFeasible i)
  | none => false

/-- **BALANCED 2-INTERVAL GRAPH RECOGNITION is NP-complete.** Source: Gambette and Vialette
(2007), Theorem 1. -/
public theorem_wanted balancedTwoIntervalGraphRecognition_npComplete :
    balancedTwoIntervalGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L balancedTwoIntervalGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BalancedTwoIntervalGraphRecognition
