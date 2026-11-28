/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs: definitions

Source:
G. J. Chang, "The weighted independent domination problem is NP-complete for chordal graphs",
Discrete Applied Mathematics 143 (2004), 351-352, doi:10.1016/j.dam.2003.05.004;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), Journal of
Algorithms 5 (1984), 147-160, doi:10.1016/0196-6774(84)90045-2 (records the result as a personal
communication of Chang to Farber, and that 0/1 weights are polynomial by Farber's algorithm);
K. Khoshkhah, M. Khosravian Ghadikolaei, J. Monnot and F. Sikora, "Weighted upper edge cover:
complexity and approximability", Journal of Graph Algorithms and Applications 24 (2020),
doi:10.7155/jgaa.00519 (records that Chang's result holds with two positive weight values).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordal

/-- An instance: the vertex count `n` (vertices `0, ..., n - 1`), the edge list, the vertex
weights `w(0), ..., w(n - 1)`, and the bound `B`. -/
abbrev WeightedIndependentDominatingSetChordalInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedIndependentDominatingSetChordalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one weight
per vertex, and the graph is chordal (no induced cycle of length at least `4`). -/
def WellFormed (i : WeightedIndependentDominatingSetChordalInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧
    ∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)

/-- Some independent dominating set has total weight at most `B`. -/
def WeightedIndependentDominatingSetChordalFeasible
    (i : WeightedIndependentDominatingSetChordalInstance) : Prop :=
  ∃ D : Finset (Fin i.1), (Graph i).IsIndepDominating (D : Set (Fin i.1)) ∧
    ∑ v ∈ D, i.2.2.1.getD v 0 ≤ i.2.2.2

open Classical in
/-- WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs as a decision problem over
bitstrings. -/
noncomputable def weightedIndependentDominatingSetChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedIndependentDominatingSetChordalInstance) x with
  | some i => decide (WellFormed i ∧ WeightedIndependentDominatingSetChordalFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordal
