/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM MINIMUM METRIC K-SPANNING TREE: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MAXIMUM MINIMUM METRIC K-SPANNING TREE (decision version);
M. M. Halldórsson, K. Iwano, N. Katoh, and T. Tokuyama, "Finding subsets maximizing minimum
structures", SIAM Journal on Discrete Mathematics 12 (1999), 342-359,
doi:10.1137/S0895480196309791.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree

/-- An instance: the number `n` of vertices, the length matrix as `n` rows of `n` entries
(`l(a, b)` is entry `b` of row `a`), the size `k`, and the bound `K`. -/
abbrev MaximumMinimumMetricKSpanningTreeInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- The length `l(a, b)`: entry `b` of row `a` of the matrix (`0` outside it). -/
def dist (i : MaximumMinimumMetricKSpanningTreeInstance) (a b : ℕ) : ℕ :=
  (i.2.1.getD a []).getD b 0

/-- Well-formedness of an instance: the matrix has `n` rows of `n` entries and is a metric
(`l(a, a) = 0`, `0 < l(a, b)` for `a ≠ b`, `l(a, b) = l(b, a)`, `l(a, c) ≤ l(a, b) + l(b, c)`),
and `1 ≤ k ≤ n`. -/
def WellFormed (i : MaximumMinimumMetricKSpanningTreeInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ a < i.1, dist i a a = 0) ∧ (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < dist i a b) ∧
    (∀ a < i.1, ∀ b < i.1, dist i a b = dist i b a) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1, dist i a c ≤ dist i a b + dist i b c) ∧
    1 ≤ i.2.2.1 ∧ i.2.2.1 ≤ i.1

/-- The length of an edge `{u, v}` between vertices of `V'`: `min (l(u, v), l(v, u))`. -/
def edgeLength (i : MaximumMinimumMetricKSpanningTreeInstance) (V' : Finset (Fin i.1)) :
    Sym2 V' → ℕ :=
  Sym2.lift ⟨fun a b => min (dist i a.1 b.1) (dist i b.1 a.1), fun _ _ => min_comm _ _⟩

open Classical in
/-- Some set `V'` of `k` vertices has every tree on `V'` of total edge length at least `K`. -/
def MaximumMinimumMetricKSpanningTreeFeasible
    (i : MaximumMinimumMetricKSpanningTreeInstance) : Prop :=
  ∃ V' : Finset (Fin i.1), V'.card = i.2.2.1 ∧
    ∀ T : SimpleGraph V', T.IsTree → i.2.2.2 ≤ ∑ e ∈ T.edgeFinset, edgeLength i V' e

open Classical in
/-- MAXIMUM MINIMUM METRIC K-SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def maximumMinimumMetricKSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumMinimumMetricKSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MaximumMinimumMetricKSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree
