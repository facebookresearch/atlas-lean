/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED GRAPH EMBEDDABILITY on the line (K = 1): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedGraphEmbeddabilityLine

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

end MetaMathlibExt.Complexity.NPComplete.WeightedGraphEmbeddabilityLine
