/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF COMPARABILITY GRAPHS OF DIMENSION-d POSETS is NP-complete

Source:
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036;
W. T. Trotter, J. I. Moore and D. P. Sumner, "The dimension of a comparability graph",
Proceedings of the American Mathematical Society 60 (1976), 35-38,
doi:10.1090/S0002-9939-1976-0417001-6 (the dimension of a poset depends only on its
comparability graph);
ISGCI, class "comparability graphs of dimension d posets" (gc_907), problem Recognition.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphDimensionRecognition

/-!
# RECOGNITION OF COMPARABILITY GRAPHS OF DIMENSION-d POSETS is NP-complete

For a fixed integer `d ≥ 3`: INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` the comparability
graph of a poset of dimension at most `d`?

The comparability graph of a strict partial order `r` on `V` joins two distinct vertices exactly
when they are comparable under `r` (as in `ComparabilityGraphSandwich.IsComparabilityGraph`,
here with the order named so that its dimension can be bounded). The dimension of a poset `P` is
the least number of linear extensions of `P` whose intersection is `P`; it is at most `d` when
some `k ≤ d` linear orderings of `V` have `P` as their intersection (repeating an ordering shows
that "at most `d`" and "exactly `d` orderings, repetitions allowed" agree for `d ≥ 1`). As in
`PartialOrderDimension.PartialOrderDimensionFeasible`, a linear ordering of `V = Fin n` is a
permutation `σ` giving each vertex its position, and `u` precedes `v` in it when `σ u < σ v`.
The ISGCI classes for fixed `d` are nested (dimension `3` inside dimension `4`, "by
definition"), so the class is read as dimension at most `d`.

Yannakakis (1982) proved that deciding whether a poset has dimension at most `d` is NP-complete
for every fixed `d ≥ 3`. Since the dimension of a poset depends only on its comparability graph
(Trotter, Moore and Sumner 1976) and comparability graphs can be recognized in polynomial time,
the same holds for this graph problem; ISGCI records it as NP-complete with Yannakakis's paper as
the reference. For `d ≤ 2` the problem is polynomial (dimension at most `2` posets have the
permutation graphs as comparability graphs), so the theorem assumes `d ≥ 3`.

The graph is given by an edge list on `Fin n`. Isolated vertices do not change the answer for
`d ≥ 2` (an element incomparable to all others can be appended to a realizer: put it last in one
ordering and first in another), so the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ComparabilityGraphDimensionRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ComparabilityGraphDimensionRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ComparabilityGraphDimensionRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The order `r` on `Fin n` has dimension at most `d`: there are `k ≤ d` linear orderings of the
elements (`σ j` gives each element its position in the `j`-th ordering) such that `r u v` holds
if and only if `u` precedes `v` in each of them. -/
def HasDimensionAtMost {n : ℕ} (r : Fin n → Fin n → Prop) (d : ℕ) : Prop :=
  ∃ k ≤ d, ∃ σ : Fin k → Equiv.Perm (Fin n), ∀ u v : Fin n, r u v ↔ ∀ j : Fin k, σ j u < σ j v

/-- `H` is the comparability graph of a poset of dimension at most `d`: some strict partial order
`r` on the vertices (Mathlib's `IsStrictOrder`) makes two vertices adjacent exactly when they are
comparable under `r`, and `r` has dimension at most `d`. -/
def IsComparabilityGraphOfDimensionAtMost {n : ℕ} (H : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∃ r : Fin n → Fin n → Prop, IsStrictOrder (Fin n) r ∧
    (∀ u v, H.Adj u v ↔ r u v ∨ r v u) ∧ HasDimensionAtMost r d

/-- The graph of the instance is the comparability graph of a poset of dimension at most `d`. -/
def ComparabilityGraphDimensionRecognitionFeasible (d : ℕ)
    (i : ComparabilityGraphDimensionRecognitionInstance) : Prop :=
  IsComparabilityGraphOfDimensionAtMost (Graph i) d

open Classical in
/-- RECOGNITION OF COMPARABILITY GRAPHS OF DIMENSION-`d` POSETS as a decision problem over
bitstrings. -/
noncomputable def comparabilityGraphDimensionRecognitionDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparabilityGraphDimensionRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ ComparabilityGraphDimensionRecognitionFeasible d i)
  | none => false

/-- **RECOGNITION OF COMPARABILITY GRAPHS OF DIMENSION-d POSETS is NP-complete.** For every fixed
`d ≥ 3`, deciding whether a graph is the comparability graph of a poset of dimension at most `d`
is NP-complete. Source: Yannakakis (1982); Trotter, Moore and Sumner (1976); ISGCI gc_907. -/
public theorem_wanted comparabilityGraphDimensionRecognition_npComplete (d : ℕ) (_hd : 3 ≤ d) :
    comparabilityGraphDimensionRecognitionDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (comparabilityGraphDimensionRecognitionDec d)

end MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphDimensionRecognition
