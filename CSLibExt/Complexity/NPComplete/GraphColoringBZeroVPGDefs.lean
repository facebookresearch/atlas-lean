/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON B₀-VPG GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
A. Asinowski, E. Cohen, M. C. Golumbic, V. Limouzy, M. Lipshteyn, and M. Stern, "Vertex
intersection graphs of paths on a grid", Journal of Graph Algorithms and Applications 16 (2012),
129-150, doi:10.7155/jgaa.00253, Theorem 8.
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringBZeroVPG

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- The graph is a `B₀`-VPG graph: vertex `v` gets the grid segment `Set.Icc (lo v) (hi v)` of
`ℕ × ℕ`, horizontal or vertical (its endpoints agree in one coordinate), and two distinct
vertices are adjacent exactly when their segments share a grid point. -/
def IsBZeroVPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ lo hi : Fin n → ℕ × ℕ, (∀ v, lo v ≤ hi v ∧ ((lo v).1 = (hi v).1 ∨ (lo v).2 = (hi v).2)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (Set.Icc (lo u) (hi u) ∩ Set.Icc (lo v) (hi v)).Nonempty)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `3 ≤ m ≤ |V|`
whose graph is a `B₀`-VPG graph. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (3 ≤ i.2.2 ∧ i.2.2 ≤ i.1) ∧ IsBZeroVPG (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY ON B₀-VPG GRAPHS as a decision problem over bitstrings. -/
noncomputable def graphColoringBZeroVPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringBZeroVPG
