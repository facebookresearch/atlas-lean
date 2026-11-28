/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER, radius `K` or greater for trees,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205,
comment: the variant asking for an assignment yielding diameter `K` or greater is NP-complete
for trees in the radius case (reference: Y. Perl and S. Zaks (1978), private communication);
see also Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical
Computer Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedRadiusAtLeastTrees

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the collection `C` of edge
lengths as a list, and the bound `K`. -/
abbrev WeightedRadiusInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedRadiusInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The length of the edge `s` when the `j`-th edge of the edge list has length `w[j]`: the
length paired with the list entry whose endpoints are the endpoints of `s` (unique under
`WellFormed`). -/
def edgeLength (i : WeightedRadiusInstance) (w : List ℕ) (s : Sym2 (Fin i.1)) : ℕ :=
  (((i.2.1.zip w).find? fun e => s.map Fin.val = s(e.1.1, e.1.2)).map fun e => e.2).getD 0

/-- The length of a walk under the edge lengths `w`: the sum of the lengths of its edges. -/
def walkLength (i : WeightedRadiusInstance) (w : List ℕ) {u v : Fin i.1}
    (p : (Graph i).Walk u v) : ℕ :=
  (p.edges.map (edgeLength i w)).sum

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), that graph is a tree,
`C` has `|E|` members, and `K` is positive. -/
def WellFormed (i : WeightedRadiusInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsTree ∧ i.2.2.1.length = i.2.1.length ∧ 0 < i.2.2.2

/-- Some rearrangement `w` of `C`, taken as the edge lengths, gives `G` radius `K` or greater:
for every vertex `v` some vertex `u` has every path from `v` to `u` of length at least `K`. -/
def WeightedRadiusFeasible (i : WeightedRadiusInstance) : Prop :=
  ∃ w : List ℕ, w.Perm i.2.2.1 ∧ ∀ v : Fin i.1, ∃ u : Fin i.1,
    ∀ p : (Graph i).Walk v u, p.IsPath → i.2.2.2 ≤ walkLength i w p

open Classical in
/-- WEIGHTED DIAMETER, radius `K` or greater for trees, as a decision problem over bitstrings. -/
noncomputable def weightedRadiusAtLeastTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedRadiusInstance) x with
  | some i => decide (WellFormed i ∧ WeightedRadiusFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedRadiusAtLeastTrees
