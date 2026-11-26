/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on circle graphs is NP-complete

Source:
J. M. Keil, "The complexity of domination problems in circle graphs", Discrete Applied
Mathematics 42(1) (1993), 51-63, doi:10.1016/0166-218X(93)90178-Q;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph

/-!
# DOMINATING SET on circle graphs is NP-complete

INSTANCE: a circle graph `G`, given by a chord model (a family of chords of a circle, one per
vertex, two vertices adjacent when their chords cross), and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K` (every vertex not in `V'` has a
neighbor in `V'`)?

A chord is given by its two endpoints, natural numbers `a < b` naming points in clockwise
order on the circle; the endpoints of all chords are distinct. Two chords `(a, b)` and `(c, d)`
with distinct endpoints cross exactly when their endpoints interleave, `a < c < b < d` or
`c < a < d < b`; nested or disjoint chords do not meet. Every circle graph has such a model.
Domination is `SimpleGraph.IsDominating` from `MathlibExt.Combinatorics.SimpleGraph.Domination`.
The bound `K ≤ |V|` follows the instance class of [GT2] DOMINATING SET.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the chords as pairs of endpoint positions, one per vertex, and the bound `K`;
increasing and distinct endpoints are checked by `WellFormed`. -/
abbrev DominatingSetCircleGraphInstance := List (ℕ × ℕ) × ℕ

/-- The circle graph of a chord model: two distinct chords are adjacent when their endpoints
interleave. -/
def circleGraph (C : List (ℕ × ℕ)) : SimpleGraph (Fin C.length) :=
  SimpleGraph.fromRel fun j k => C[j].1 < C[k].1 ∧ C[k].1 < C[j].2 ∧ C[j].2 < C[k].2

/-- Well-formedness of an instance: every chord has endpoints `a < b`, all endpoints of all
chords are distinct, and `1 ≤ K ≤ |V|`. -/
def WellFormed (i : DominatingSetCircleGraphInstance) : Prop :=
  (∀ c ∈ i.1, c.1 < c.2) ∧ (i.1.flatMap fun c => [c.1, c.2]).Nodup ∧ 1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- The circle graph has a dominating set of at most `K` vertices. -/
def DominatingSetCircleGraphFeasible (i : DominatingSetCircleGraphInstance) : Prop :=
  ∃ D : Finset (Fin i.1.length), D.card ≤ i.2 ∧ (circleGraph i.1).IsDominating ↑D

open Classical in
/-- DOMINATING SET on circle graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetCircleGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetCircleGraphInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetCircleGraphFeasible i)
  | none => false

/-- **DOMINATING SET on circle graphs is NP-complete.** Source: Keil (1993). -/
public theorem_wanted dominatingSetCircleGraph_npComplete :
    dominatingSetCircleGraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetCircleGraphDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph
