/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER, diameter `K` or greater,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205,
comment: the variant asking for an assignment yielding diameter `K` or greater is NP-complete in
the strong sense for general graphs (reference: Y. Perl and S. Zaks (1978), private
communication); see also Y. Perl and S. Zaks, "On the complexity of edge labelings for trees",
Theoretical Computer Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the collection `C` of edge
lengths as a list, and the bound `K`. -/
abbrev WeightedDiameterInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedDiameterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The length of the edge `s` when the `j`-th edge of the edge list has length `w[j]`: the
length paired with the list entry whose endpoints are the endpoints of `s` (unique under
`WellFormed`). -/
def edgeLength (i : WeightedDiameterInstance) (w : List ℕ) (s : Sym2 (Fin i.1)) : ℕ :=
  (((i.2.1.zip w).find? fun e => s.map Fin.val = s(e.1.1, e.1.2)).map fun e => e.2).getD 0

/-- The length of a walk under the edge lengths `w`: the sum of the lengths of its edges. -/
def walkLength (i : WeightedDiameterInstance) (w : List ℕ) {u v : Fin i.1}
    (p : (Graph i).Walk u v) : ℕ :=
  (p.edges.map (edgeLength i w)).sum

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `C` has `|E|`
members, and `K` is positive. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.2.1.length ∧ 0 < i.2.2.2

/-- Some rearrangement `w` of `C`, taken as the edge lengths, gives `G` diameter `K` or greater:
some pair `u, v` of vertices has every path from `u` to `v` of length at least `K`. -/
def WeightedDiameterFeasible (i : WeightedDiameterInstance) : Prop :=
  ∃ w : List ℕ, w.Perm i.2.2.1 ∧ ∃ u v : Fin i.1,
    ∀ p : (Graph i).Walk u v, p.IsPath → i.2.2.2 ≤ walkLength i w p

open Classical in
/-- WEIGHTED DIAMETER, diameter `K` or greater, as a decision problem over bitstrings. -/
noncomputable def weightedDiameterAtLeastDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast
