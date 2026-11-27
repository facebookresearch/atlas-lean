/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE CROSSING NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, "Crossing number is NP-complete", SIAM Journal on Algebraic and
Discrete Methods 4(3) (1983), 312-316, doi:10.1137/0604033 (the bipartite crossing number
problem for bipartite multigraphs, the intermediate step of the proof, by a transformation from
OPTIMAL LINEAR ARRANGEMENT [GT42]);
C. Buchheim, M. Chimani, C. Gutwenger, M. Jünger and P. Mutzel, "Crossings and planarization",
in R. Tamassia (ed.), *Handbook of Graph Drawing and Visualization*, CRC Press (2013), chapter 2,
Section 2.3.1, Lemma 2.1 (statement of the problem and a reproduction of the proof).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OneSidedCrossingMinimizationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteCrossingNumber

open OneSidedCrossingMinimization (crossings)

/-!
# BIPARTITE CROSSING NUMBER is NP-complete

INSTANCE: a bipartite multigraph `G = (V₁, V₂, E)` and a nonnegative integer `K`.
QUESTION: is there a drawing of `G` inside the unit square with all vertices of `V₁` on the
northern side, all vertices of `V₂` on the southern side, and at most `K` edge crossings?

Both vertex orders are free; fixing the order of one side gives ONE-SIDED CROSSING MINIMIZATION
(`OneSidedCrossingMinimizationWanted`). Garey and Johnson prove this problem NP-complete for
multigraphs, as the intermediate step of their proof that CROSSING NUMBER is NP-complete; the
multigraph their transformation builds has `|E|²` parallel copies of the edges `uᵢwᵢ`.

The two vertex classes are listed explicitly, as duplicate-free lists of natural-number names
(the order of the lists is irrelevant), and the edges are pairs `(u, w)` with `u ∈ V₁` and
`w ∈ V₂`; the edge list may repeat a pair (parallel edges of a multigraph). A drawing determines
an order of `V₁` along the northern side and of `V₂` along the southern side, given here as
permutations of the two lists. For given orders the fewest crossings is the number counted by
`OneSidedCrossingMinimization.crossings`: two edges whose endpoints appear in opposite orders on
the two sides have interleaved endpoints on the boundary of the square and must cross, and the
straight-line drawing (parallel copies drawn as nearly straight, non-crossing curves) has no
other crossings; edges sharing an endpoint, in particular parallel copies, are not counted. The
crossing count runs over ordered pairs of edge-list entries, so each crossing pair of edges
counts once and a pair crossing `m` parallel copies counts `m` times.

Membership in NP: the two orders are a polynomial certificate, and the count takes `O(|E|²)`
time over the explicit edge list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertices of `V₁`, the vertices of `V₂`, the edges `(u, w)` (repetitions
allowed), and the bound `K`. -/
abbrev BipartiteCrossingNumberInstance := List ℕ × List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `V₁` and `V₂` are listed without repetition, and every edge
joins a vertex of `V₁` to a vertex of `V₂`. -/
def WellFormed (i : BipartiteCrossingNumberInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 ∈ i.1 ∧ e.2 ∈ i.2.1

/-- Some order of `V₁` and some order of `V₂` give a two-sided drawing with at most `K`
crossings. -/
def BipartiteCrossingNumberFeasible (i : BipartiteCrossingNumberInstance) : Prop :=
  ∃ order₁ order₂ : List ℕ, order₁.Perm i.1 ∧ order₂.Perm i.2.1 ∧
    crossings order₁ order₂ i.2.2.1 ≤ i.2.2.2

open Classical in
/-- BIPARTITE CROSSING NUMBER as a decision problem over bitstrings. -/
noncomputable def bipartiteCrossingNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteCrossingNumberInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteCrossingNumberFeasible i)
  | none => false

/-- **BIPARTITE CROSSING NUMBER is NP-complete.** Source: Garey and Johnson (1983). -/
public theorem_wanted bipartiteCrossingNumber_npComplete :
    bipartiteCrossingNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteCrossingNumberDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteCrossingNumber
