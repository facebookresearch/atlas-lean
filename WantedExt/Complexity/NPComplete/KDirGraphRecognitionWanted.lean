/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-DIR GRAPH RECOGNITION is NP-complete for every fixed k ≥ 2

Source:
J. Kratochvíl and J. Matoušek, "NP-hardness results for intersection graphs",
Commentationes Mathematicae Universitatis Carolinae 30 (1989), no. 4, 761-773,
http://dml.cz/dmlcz/106799 (Theorem 1 and Proposition 5);
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (the case `k = 2`);
J. Kratochvíl and J. Matoušek, "Intersection graphs of segments", Journal of Combinatorial
Theory, Series B 62 (1994), 289-315, doi:10.1006/jctb.1994.1071 (membership in NP);
ISGCI (https://www.graphclasses.org/classes/gc_935.html), problem "Recognition" on 3-DIR
graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KDirGraphRecognition

/-!
# k-DIR GRAPH RECOGNITION is NP-complete for every fixed k ≥ 2

Fix an integer `k ≥ 2`.
INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a `k`-DIR graph, that is, the intersection graph of straight line segments in
the plane whose slopes lie among at most `k` real numbers?

Kratochvíl and Matoušek (1989), Section 2: "k-DIR(d₁, …, d_k) = IG({all segments with slopes
among d₁, …, d_k}), d₁, …, d_k real numbers, k-DIR = ⋃ {k-DIR(d₁, …, d_k); d₁, …, d_k real
numbers}", where `IG(C)` is the class of graphs `G = (V, E)` with `V ⊆ C` and `uv ∈ E` iff
`u ∩ v ≠ ∅`. Their Theorem 1 states that RECOG(k-DIR) is NP-complete for every `k ≥ 2`
(Proposition 5; the case `k = 2` is proved in detail in Kratochvíl (1994)), and their remark
after it attributes membership in NP, for every fixed `k`, to Kratochvíl and Matoušek (1994).
Segments of the same slope may overlap; forbidding that gives the different class PURE-k-DIR.

`IsKDirGraph k H` chooses slopes `s : Fin k → ℝ` (not necessarily distinct, so at most `k`
directions), and for each vertex `v` a slope index `c v` and the closed segment
`SimpleGraph.Segment (a v) (b v)` from `a v` to `b v` with `(a v).1 < (b v).1` and
`(b v).2 - (a v).2 = s (c v) * ((b v).1 - (a v).1)`: a non-degenerate segment of slope
`s (c v)`. Two distinct vertices are adjacent exactly when their segments share a point. Two
vertices may get the same segment; such a pair can always be split by lengthening one of
the two segments slightly along its line, so this is the same graph class as with `V ⊆ C`.
The graph is given by an edge list on `Fin n` as in the other graph statements of this
directory (`Cslib.Complexity.Karp.edgeGraph`).

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
abbrev KDirGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : KDirGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : KDirGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `k`-DIR graph: there are slopes `s j` (`j : Fin k`) and, for each vertex `v`, a
non-degenerate closed segment from `a v` to `b v` whose slope is `s (c v)`, such that two
distinct vertices are adjacent in `H` exactly when their segments intersect. -/
def IsKDirGraph (k : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (s : Fin k → ℝ) (a b : Fin n → ℝ × ℝ) (c : Fin n → Fin k),
    (∀ v, (a v).1 < (b v).1 ∧ (b v).2 - (a v).2 = s (c v) * ((b v).1 - (a v).1)) ∧
      ∀ u v, u ≠ v →
        (H.Adj u v ↔
          (SimpleGraph.Segment (a u) (b u) ∩ SimpleGraph.Segment (a v) (b v)).Nonempty)

/-- The graph of the instance is a `k`-DIR graph. -/
def KDirGraphRecognitionFeasible (k : ℕ) (i : KDirGraphRecognitionInstance) : Prop :=
  IsKDirGraph k (Graph i)

open Classical in
/-- k-DIR GRAPH RECOGNITION, for the fixed number of slopes `k`, as a decision problem over
bitstrings. -/
noncomputable def kDirGraphRecognitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KDirGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ KDirGraphRecognitionFeasible k i)
  | none => false

/-- **k-DIR GRAPH RECOGNITION is NP-complete for every fixed `k ≥ 2`.** Source: Kratochvíl and
Matoušek (1989), Theorem 1; Kratochvíl (1994) for `k = 2`; membership in NP: Kratochvíl and
Matoušek (1994). -/
public theorem_wanted kDirGraphRecognition_npComplete (k : ℕ) (hk : 2 ≤ k) :
    kDirGraphRecognitionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kDirGraphRecognitionDec k)

end MetaMathlibExt.Complexity.NPComplete.KDirGraphRecognition
