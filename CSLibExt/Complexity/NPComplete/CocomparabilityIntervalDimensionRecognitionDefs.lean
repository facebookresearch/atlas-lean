/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF CO-COMPARABILITY GRAPHS OF POSETS OF INTERVAL DIMENSION d: definitions

Source:
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036;
M. Habib, D. Kelly and R. H. Möhring, "Interval dimension is a comparability invariant",
Discrete Mathematics 88 (1991), 211-229, doi:10.1016/0012-365X(91)90010-Y;
H. L. Bodlaender, T. Kloks, D. Kratsch and H. Müller, "Treewidth and minimum fill-in on
d-trapezoid graphs", Journal of Graph Algorithms and Applications 2(5) (1998), 1-23,
doi:10.7155/jgaa.00008 (Theorem 14 and the remarks after it);
ISGCI, class "co-comparability graphs of posets of interval dimension d" (gc_905), problem
Recognition.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev CocomparabilityIntervalDimensionRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CocomparabilityIntervalDimensionRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CocomparabilityIntervalDimensionRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The order `r` on `Fin n` has interval dimension at most `d`: there are `k ≤ d` interval
orders (in the `j`-th one, element `v` has the closed real interval `[l j v, h j v]`, and `u`
precedes `v` when `h j u < l j v`) such that `r u v` holds if and only if `u` precedes `v` in
each of them. -/
def HasIntervalDimensionAtMost {n : ℕ} (r : Fin n → Fin n → Prop) (d : ℕ) : Prop :=
  ∃ k ≤ d, ∃ l h : Fin k → Fin n → ℝ, (∀ j v, l j v ≤ h j v) ∧
    ∀ u v : Fin n, r u v ↔ ∀ j : Fin k, h j u < l j v

/-- `H` is the co-comparability graph of a poset of interval dimension at most `d`: some strict
partial order `r` on the vertices (Mathlib's `IsStrictOrder`) makes two vertices adjacent in the
complement `Hᶜ` exactly when they are comparable under `r`, and `r` has interval dimension at
most `d`. -/
def IsCocomparabilityGraphOfIntervalDimensionAtMost {n : ℕ} (H : SimpleGraph (Fin n))
    (d : ℕ) : Prop :=
  ∃ r : Fin n → Fin n → Prop, IsStrictOrder (Fin n) r ∧
    (∀ u v, Hᶜ.Adj u v ↔ r u v ∨ r v u) ∧ HasIntervalDimensionAtMost r d

/-- The graph of the instance is the co-comparability graph of a poset of interval dimension at
most `d`. -/
def CocomparabilityIntervalDimensionRecognitionFeasible (d : ℕ)
    (i : CocomparabilityIntervalDimensionRecognitionInstance) : Prop :=
  IsCocomparabilityGraphOfIntervalDimensionAtMost (Graph i) d

open Classical in
/-- RECOGNITION OF CO-COMPARABILITY GRAPHS OF POSETS OF INTERVAL DIMENSION `d` as a decision
problem over bitstrings. -/
noncomputable def cocomparabilityIntervalDimensionRecognitionDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CocomparabilityIntervalDimensionRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ CocomparabilityIntervalDimensionRecognitionFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CocomparabilityIntervalDimensionRecognition
