/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER, diameter `K` or greater, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205,
comment: the variant asking for an assignment yielding diameter `K` or greater is NP-complete in
the strong sense for general graphs (reference: Y. Perl and S. Zaks (1978), private
communication); see also Y. Perl and S. Zaks, "On the complexity of edge labelings for trees",
Theoretical Computer Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast

/-!
# WEIGHTED DIAMETER, diameter `K` or greater, is NP-complete

INSTANCE: a graph `G = (V, E)`, a collection `C` of `|E|` not necessarily distinct non-negative
integers, and a positive integer `K`. QUESTION: is there a one-to-one function `f : E → C` such
that, if `f(e)` is taken as the length of edge `e`, then `G` has diameter `K` or greater?

This is the variant of WEIGHTED DIAMETER (diameter `K` or less: every pair of vertices is joined
by a path of length `K` or less) that Garey and Johnson's comment records; it is NP-complete in
the strong sense for general graphs. "Diameter `K` or greater" is read as the negation of that
condition for `K - 1`: some pair `u, v` of vertices is joined by no path of length less than
`K`, i.e., every path from `u` to `v` has length at least `K`. Under this reading, which is the
usual convention that a disconnected graph has infinite diameter, a disconnected graph is a
yes-instance. A path is a Mathlib `SimpleGraph.Walk` that `IsPath`, and its length is the sum of
the lengths of its edges.

`C` is a list of length `|E|`, and the one-to-one function `f : E → C` is a rearrangement `w` of
that list (`List.Perm`): the `j`-th edge of the edge list gets length `w[j]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Numbers use the canonical binary
encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **WEIGHTED DIAMETER, diameter `K` or greater, is NP-complete.** Source: Garey and Johnson
(1979), [GT65], comment (Perl and Zaks, 1978). -/
public theorem_wanted weightedDiameterAtLeast_npComplete :
    weightedDiameterAtLeastDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedDiameterAtLeastDec

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterAtLeast
