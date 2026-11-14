/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN7] PARTIAL ORDER
DIMENSION;
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimension

/-!
# PARTIAL ORDER DIMENSION is NP-complete

An instance is a directed acyclic graph `G = (V, A)` that is transitive (whenever `(u, v)` and
`(v, w)` are arcs, so is `(u, w)`), and a positive integer `K ≤ |V|²`. The question is whether
there is a collection of `k ≤ K` linear orderings of `V` such that `(u, v)` is an arc if and
only if `u` precedes `v` in each of the orderings, i.e. whether the partial order `A` has
dimension at most `K`. Garey and Johnson list this as open problem [OPEN7]; Yannakakis (1982)
proved it NP-complete already for `K = 3`.

The digraph is given by its `n × n` adjacency matrix, so the encoding has at least `n²` bits
and a realizer of `k ≤ K ≤ n²` orderings is a certificate of polynomial size. (An arc list
with a binary vertex count would let `O(log n)` bits describe `n` isolated vertices.) A linear
ordering of `V = Fin n` is a permutation `σ` giving each vertex its position: `u` precedes `v`
in `σ` when `σ u < σ v`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the adjacency matrix of the digraph (row `u`, column `v` is `true` when
`(u, v)` is an arc; vertices are `0, …, n - 1` for `n` rows), and the bound `K`. -/
abbrev PartialOrderDimensionInstance := List (List Bool) × ℕ

/-- The arc relation of the instance on `Fin n`, `n` the number of matrix rows. -/
def Arc (i : PartialOrderDimensionInstance) (u v : Fin i.1.length) : Prop :=
  (i.1.getD u []).getD v false = true

/-- Well-formedness of an instance: the matrix is `n × n`, the digraph is acyclic (no vertex
reaches itself by a nonempty directed path) and transitive, and `0 < K ≤ |V|²`. -/
def WellFormed (i : PartialOrderDimensionInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ v : Fin i.1.length, ¬ Relation.TransGen (Arc i) v v) ∧
    (∀ u v w : Fin i.1.length, Arc i u v → Arc i v w → Arc i u w) ∧
    0 < i.2 ∧ i.2 ≤ i.1.length ^ 2

/-- There are `k ≤ K` linear orderings of the vertices such that `(u, v)` is an arc if and
only if `u` precedes `v` in each of them. -/
def PartialOrderDimensionFeasible (i : PartialOrderDimensionInstance) : Prop :=
  ∃ k ≤ i.2, ∃ σ : Fin k → Equiv.Perm (Fin i.1.length),
    ∀ u v : Fin i.1.length, Arc i u v ↔ ∀ j : Fin k, σ j u < σ j v

open Classical in
/-- PARTIAL ORDER DIMENSION as a decision problem over bitstrings. -/
noncomputable def partialOrderDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartialOrderDimensionInstance) x with
  | some i => decide (WellFormed i ∧ PartialOrderDimensionFeasible i)
  | none => false

/-- **PARTIAL ORDER DIMENSION is NP-complete.** Source: Garey and Johnson (1979), [OPEN7];
Yannakakis (1982). -/
public theorem_wanted partialOrderDimension_npComplete :
    partialOrderDimensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialOrderDimensionDec

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimension
