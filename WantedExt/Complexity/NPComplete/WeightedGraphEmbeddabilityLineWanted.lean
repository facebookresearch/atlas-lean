/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED GRAPH EMBEDDABILITY on the line (K = 1) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 89-99,
doi:10.1016/0196-6774(82)90011-6, problem [5] WEIGHTED GRAPH EMBEDDABILITY;
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2 (update on WEIGHTED GRAPH EMBEDDABILITY: the `K = 1` case is
NP-complete if the weights come from `{1, 2}`);
J. B. Saxe, "Embeddability of weighted graphs in k-space is strongly NP-hard", Proc. 17th
Allerton Conference on Communication, Control, and Computing (1979), 480-489;
J. B. Saxe, "Two papers on graph embedding problems", Report CMU-CS-80-102, Department of
Computer Science, Carnegie-Mellon University (1980).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedGraphEmbeddabilityLine

/-!
# WEIGHTED GRAPH EMBEDDABILITY on the line (K = 1) is NP-complete

INSTANCE: a graph `G = (V, E)` and a weight `w(u, v) ∈ ℤ⁺` for each edge `{u, v} ∈ E`.
QUESTION: is there a function `f : V → ℝ` (not necessarily one-to-one) such that for all
`{u, v} ∈ E`, the distance `|f(u) - f(v)|` between `f(u)` and `f(v)` equals the weight
`w(u, v)`?

This is Johnson's WEIGHTED GRAPH EMBEDDABILITY (column of March 1982, problem [5]: an embedding
`f : V → ℝᴷ` in which the Euclidean distance between `f(u)` and `f(v)` equals `w(u, v)` for every
edge) with the dimension fixed to `K = 1`, where the Euclidean distance on `ℝ` is `|x - y|`. The
column of March 1984 corrects the `K = 1` case: it is in P if all weights are equal and
NP-complete if the weights come from the set `{1, 2}` (Saxe's report CMU-CS-80-102); Saxe's
Allerton paper reduces 3SAT to it.

The graph is given by its number of vertices `n` (vertices `0, …, n - 1`) and a list of weighted
edges `(u, v, w)`; the endpoint pairs form a simple edge list (no duplicate edges in either
orientation, no self-loops, endpoints in range), so each edge carries one weight, and every
weight is positive. Weights are encoded in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of vertices `n` and the weighted edges `(u, v, w)`. -/
abbrev WeightedGraphEmbeddabilityLineInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: the endpoint pairs describe a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and every weight is
positive. -/
def WellFormed (i : WeightedGraphEmbeddabilityLineInstance) : Prop :=
  (i.2.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ (i.2.map fun e => (e.1, e.2.1)) ∧ 0 < e.2.2

/-- Some placement `f` of the vertices on the real line puts the ends of every edge at distance
equal to the edge's weight. -/
def WeightedGraphEmbeddabilityLineFeasible (i : WeightedGraphEmbeddabilityLineInstance) :
    Prop :=
  ∃ f : Fin i.1 → ℝ, ∀ e ∈ i.2, ∀ (hu : e.1 < i.1) (hv : e.2.1 < i.1),
    |f ⟨e.1, hu⟩ - f ⟨e.2.1, hv⟩| = (e.2.2 : ℝ)

open Classical in
/-- WEIGHTED GRAPH EMBEDDABILITY on the line as a decision problem over bitstrings. -/
noncomputable def weightedGraphEmbeddabilityLineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedGraphEmbeddabilityLineInstance) x with
  | some i => decide (WellFormed i ∧ WeightedGraphEmbeddabilityLineFeasible i)
  | none => false

/-- **WEIGHTED GRAPH EMBEDDABILITY on the line (K = 1) is NP-complete.** Source: Johnson,
NP-completeness columns (1982, problem [5]; 1984); Saxe (1979, 1980). -/
public theorem_wanted weightedGraphEmbeddabilityLine_npComplete :
    weightedGraphEmbeddabilityLineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedGraphEmbeddabilityLineDec

end MetaMathlibExt.Complexity.NPComplete.WeightedGraphEmbeddabilityLine
