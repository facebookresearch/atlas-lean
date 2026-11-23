/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS OF ARCS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS,
p. 203 (comment: "Variant in which the "forbidden pairs" are arcs instead of vertices is also
NP-complete under the same restrictions.");
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsOfArcs

/-!
# PATH WITH FORBIDDEN PAIRS OF ARCS is NP-complete

Given a directed graph `G = (V, A)`, specified vertices `s, t ∈ V`, and a collection
`C = {(a₁, b₁), ..., (aₙ, bₙ)}` of pairs of arcs from `A`, is there a directed path from `s` to
`t` in `G` that contains at most one arc from each pair in `C`?

This is the arc variant of PATH WITH FORBIDDEN PAIRS ([GT54], `PathWithForbiddenPairsWanted`),
in which the forbidden pairs are arcs instead of vertices. The vertices are `0, ..., m - 1`;
the arcs are a list of ordered pairs (`(u, v)` is the arc `u → v`) and `C` is a list of pairs
of listed arcs. A path is, as in `PathWithForbiddenPairsWanted`, a nonempty list of distinct
vertices, starting at `s` and ending at `t`, in which consecutive vertices are joined by an arc
(`List.IsChain`); for `s = t` the one-vertex path `[s]` counts. The arcs a path `p` contains
are those joining consecutive vertices, the list `p.zip p.tail`. "At most one arc from each
pair" means that a path containing both `aⱼ` and `bⱼ` has `aⱼ = bⱼ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `m`, arc list, source `s`, target `t`, and the list `C` of pairs
of arcs. -/
abbrev PathWithForbiddenPairsOfArcsInstance :=
  ℕ × List (ℕ × ℕ) × ℕ × ℕ × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- Well-formedness of an instance: the arcs, `s` and `t` use vertices below `m`, and both
members of every pair in `C` are arcs of `A`. -/
def WellFormed (i : PathWithForbiddenPairsOfArcsInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧ i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧
    ∀ c ∈ i.2.2.2.2, c.1 ∈ i.2.1 ∧ c.2 ∈ i.2.1

/-- A directed path from `s` to `t` containing at most one arc from each pair of `C`; the arcs
of the path `p` are the consecutive pairs `p.zip p.tail`. -/
def PathWithForbiddenPairsOfArcsFeasible (i : PathWithForbiddenPairsOfArcsInstance) : Prop :=
  ∃ p : List ℕ, p.head? = some i.2.2.1 ∧ p.getLast? = some i.2.2.2.1 ∧
    p.IsChain (fun u v => (u, v) ∈ i.2.1) ∧ p.Nodup ∧
      ∀ c ∈ i.2.2.2.2, c.1 ∈ p.zip p.tail → c.2 ∈ p.zip p.tail → c.1 = c.2

open Classical in
/-- PATH WITH FORBIDDEN PAIRS OF ARCS as a decision problem over bitstrings. -/
noncomputable def pathWithForbiddenPairsOfArcsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairsOfArcsInstance) x with
  | some i => decide (WellFormed i ∧ PathWithForbiddenPairsOfArcsFeasible i)
  | none => false

/-- **PATH WITH FORBIDDEN PAIRS OF ARCS is NP-complete.** Source: Garey and Johnson (1979),
[GT54], comment; Gabow, Maheshwari and Osterweil (1976). -/
public theorem_wanted pathWithForbiddenPairsOfArcs_npComplete :
    pathWithForbiddenPairsOfArcsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathWithForbiddenPairsOfArcsDec

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsOfArcs
