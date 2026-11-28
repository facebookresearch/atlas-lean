/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER
(p. 205; credited there to Perl and Zaks, 1978, transformation from 3-PARTITION);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameter

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the collection `C` of edge
lengths as a list (repetitions allowed), and the bound `K`. -/
abbrev WeightedDiameterInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedDiameterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `C` has `|E|`
members, and `K` is positive. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.2.1.length ∧ 0 < i.2.2.2

/-- The length of the edge joining `a` and `b` when the `k`-th listed edge has length `ℓ[k]`:
the length paired with the first listed edge equal to `(a, b)` or `(b, a)` (`0` if there is
none). Under `WellFormed`, exactly one listed edge joins two adjacent vertices. -/
def edgeLength (i : WeightedDiameterInstance) (ℓ : List ℕ) (a b : ℕ) : ℕ :=
  (((i.2.1.zip ℓ).find? fun p => decide (p.1 = (a, b) ∨ p.1 = (b, a))).map Prod.snd).getD 0

/-- The length of a walk when the `k`-th listed edge has length `ℓ[k]`: the sum of the lengths
of the edges it traverses. -/
def weightedLength (i : WeightedDiameterInstance) (ℓ : List ℕ) {u v : Fin i.1}
    (p : (Graph i).Walk u v) : ℕ :=
  (p.darts.map fun d => edgeLength i ℓ d.fst d.snd).sum

/-- Some assignment of the members of `C` to the edges, one member per edge, gives `G`
diameter at most `K`: a rearrangement `ℓ` of `C` (the `k`-th listed edge gets length `ℓ[k]`)
under which every pair of vertices is joined by a path of length at most `K`. -/
def WeightedDiameterFeasible (i : WeightedDiameterInstance) : Prop :=
  ∃ ℓ : List ℕ, ℓ.Perm i.2.2.1 ∧
    ∀ u v : Fin i.1, ∃ p : (Graph i).Walk u v, p.IsPath ∧ weightedLength i ℓ p ≤ i.2.2.2

open Classical in
/-- WEIGHTED DIAMETER as a decision problem over bitstrings. -/
noncomputable def weightedDiameterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameter
