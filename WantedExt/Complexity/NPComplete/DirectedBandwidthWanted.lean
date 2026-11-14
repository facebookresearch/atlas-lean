/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED BANDWIDTH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT41] DIRECTED
BANDWIDTH;
M. R. Garey, R. L. Graham, D. S. Johnson, and D. E. Knuth, "Complexity results
for bandwidth minimization", SIAM Journal on Applied Mathematics 34 (1978),
477-495, doi:10.1137/0134037.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth

/-!
# DIRECTED BANDWIDTH is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` and a positive integer `K ≤ |V|`. QUESTION: is
there a one-to-one function `f : V → {1, 2, ..., |V|}` such that, for all `(u, v) ∈ A`,
`f(u) < f(v)` and `f(v) - f(u) ≤ K`?

The vertices are `0, ..., n - 1` and the arcs are given as a list of ordered pairs, with no
self-loops and no repeated arcs. Acyclicity is part of the instance class, so it is stated in
`WellFormed`: no vertex reaches itself along one or more arcs, that is, the transitive closure
(Mathlib's `Relation.TransGen`) of the arc relation is irreflexive. A one-to-one
`f : V → {1, ..., |V|}` is a bijection. As in `WantedExt.Complexity.NPComplete.BandwidthWanted`,
it is represented by a list `perm` that is a permutation of `0, ..., n - 1`: vertex `v` sits at
position `perm.idxOf v`, and `f(v) = perm.idxOf v + 1`. The shift by one changes neither
`f(u) < f(v)` nor `f(v) - f(u)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc list (pairs `(u, v)` for arcs
from `u` to `v`), bound `K`. -/
abbrev DirectedBandwidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the arc list describes a directed acyclic graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs, and no directed cycle: no
vertex reaches itself along one or more arcs), and `0 < K ≤ |V|`. -/
def WellFormed (i : DirectedBandwidthInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ v, ¬ Relation.TransGen (fun u w => (u, w) ∈ i.2.1) v v) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- A one-to-one numbering of the vertices, given by the positions in a permutation `perm` of
`0, ..., n - 1`, under which every arc `(u, v)` goes forward (`f(u) < f(v)`) and spans at most
`K` positions (`f(v) - f(u) ≤ K`). -/
def DirectedBandwidthFeasible (i : DirectedBandwidthInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ a ∈ i.2.1, perm.idxOf a.1 < perm.idxOf a.2 ∧ perm.idxOf a.2 - perm.idxOf a.1 ≤ i.2.2

open Classical in
/-- DIRECTED BANDWIDTH as a decision problem over bitstrings. -/
noncomputable def directedBandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedBandwidthInstance) x with
  | some i => decide (WellFormed i ∧ DirectedBandwidthFeasible i)
  | none => false

/-- **DIRECTED BANDWIDTH is NP-complete.** Source: Garey and Johnson (1979), [GT41]; Garey,
Graham, Johnson, and Knuth (1978). -/
public theorem_wanted directedBandwidth_npComplete :
    directedBandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedBandwidthDec

end MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth
