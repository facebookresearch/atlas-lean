/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH BASIS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT59] INTERSECTION GRAPH BASIS;
L. T. Kou, L. J. Stockmeyer and C. K. Wong, "Covering edges by cliques with regard to keyword
conflicts and intersection graphs", Communications of the ACM 21 (1978), 135-139,
doi:10.1145/359340.359346;
J. Orlin, "Contentment in graph theory: covering graphs with cliques", Indagationes
Mathematicae (Proceedings) 80 (1977), 406-424, doi:10.1016/1385-7258(77)90055-5;
P. Erdős, A. W. Goodman and L. Pósa, "The representation of a graph by set intersections",
Canadian Journal of Mathematics 18 (1966), 106-112, doi:10.4153/CJM-1966-014-3.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphBasis

/-- An instance: vertex count `n`, edge list over `Fin n`, and the bound `K`. -/
abbrev IntersectionGraphBasisInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntersectionGraphBasisInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: a simple edge list (no duplicates in either orientation,
no loops, endpoints `< n`), so its length is `|E|`, and `0 < K ≤ |E|`. -/
def WellFormed (i : IntersectionGraphBasisInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- `G` is the intersection graph of subsets `S[v]` of a set of at most `K` elements: distinct
vertices are adjacent iff their subsets intersect. -/
def IntersectionGraphBasisFeasible (i : IntersectionGraphBasisInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ S : Fin i.1 → Finset (Fin k),
    ∀ u v, u ≠ v → ((Graph i).Adj u v ↔ (S u ∩ S v).Nonempty)

open Classical in
/-- INTERSECTION GRAPH BASIS as a decision problem over bitstrings. -/
noncomputable def intersectionGraphBasisDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionGraphBasisInstance) x with
  | some i => decide (WellFormed i ∧ IntersectionGraphBasisFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphBasis
