/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# L(2,1)-LABELING: definitions

Source:
J. R. Griggs and R. K. Yeh, "Labelling graphs with a condition at distance 2", SIAM Journal on
Discrete Mathematics 5 (1992), 586-595, doi:10.1137/0405048;
J. Fiala, T. Kloks and J. Kratochvíl, "Fixed-parameter complexity of λ-labelings", Discrete
Applied Mathematics 113 (2001), 59-72, doi:10.1016/S0166-218X(00)00387-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.L21Labeling

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, span bound `K`. -/
abbrev L21LabelingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : L21LabelingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the graph has at least one vertex (so that the maximum
label `λ(G)` is defined), the edge list describes a simple graph on `Fin n` (no duplicate edges
in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : L21LabelingInstance) : Prop :=
  0 < i.1 ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- Some labelling `f : V → {0, …, K}` has labels at least `2` apart on adjacent vertices and
at least `1` apart on vertices at distance two. -/
def L21LabelingFeasible (i : L21LabelingInstance) : Prop :=
  ∃ f : Fin i.1 → ℕ, (∀ v, f v ≤ i.2.2) ∧
    (∀ x y, (Graph i).Adj x y → 2 ≤ |(f x : ℤ) - f y|) ∧
    ∀ x y, (Graph i).dist x y = 2 → 1 ≤ |(f x : ℤ) - f y|

open Classical in
/-- L(2,1)-LABELING as a decision problem over bitstrings. -/
noncomputable def l21LabelingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := L21LabelingInstance) x with
  | some i => decide (WellFormed i ∧ L21LabelingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.L21Labeling
