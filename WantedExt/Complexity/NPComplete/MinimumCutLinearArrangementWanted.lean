/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT
LINEAR ARRANGEMENT (credited there to F. Gavril, "Some NP-complete problems on
graphs", Proc. 11th Conference on Information Sciences and Systems, Johns
Hopkins University (1977), 91-95);
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted
trees", Theoretical Computer Science 58 (1988), 209-229,
doi:10.1016/0304-3975(88)90028-X (NP-complete already for planar graphs of
maximum degree three).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement

/-!
# MINIMUM CUT LINEAR ARRANGEMENT is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`. QUESTION: is there a one-to-one
function `f : V → {1, 2, ..., |V|}` such that for all `i`, `1 ≤ i < |V|`,
`|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`? (This is the cutwidth problem.)

The vertices are `0, ..., n - 1` and the edges are given as a list of unordered pairs, one entry
per edge. A one-to-one `f : V → {1, ..., |V|}` is a bijection. As in
`WantedExt.Complexity.NPComplete.MinimumLinearArrangementWanted`, it is represented by a list
`perm` that is a permutation of `0, ..., n - 1`: vertex `v` sits at position `perm.idxOf v`, and
`f(v) = perm.idxOf v + 1`. The cut at `i` (`1 ≤ i < |V|`) is the cut after position `j = i - 1`
(`j + 1 < n`), and `f(u) ≤ i < f(v)` becomes `perm.idxOf u ≤ j < perm.idxOf v`. An edge
`{u, v}` is cut when one of its endpoints is at a position `≤ j` and the other at a position
`> j`; since the edge is unordered, both orientations of the list entry are tested. Under
`WellFormed` the edge list has one entry per edge, so the filtered list's length is the number
of cut edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list, bound `K`. -/
abbrev MinimumCutLinearArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, ..., n - 1`
(no duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- A one-to-one numbering of the vertices, given by the positions in a permutation `perm` of
`0, ..., n - 1`, such that for every cut position `j` with `j + 1 < n` at most `K` edges have
one endpoint at a position `≤ j` and the other at a position `> j`. -/
def MinimumCutLinearArrangementFeasible (i : MinimumCutLinearArrangementInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ j, j + 1 < i.1 →
      (i.2.1.filter fun e => (perm.idxOf e.1 ≤ j ∧ j < perm.idxOf e.2) ∨
        (perm.idxOf e.2 ≤ j ∧ j < perm.idxOf e.1)).length ≤ i.2.2

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementFeasible i)
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT is NP-complete.** Source: Garey and Johnson (1979),
[GT44] (Gavril 1977); Monien and Sudborough (1988). -/
public theorem_wanted minimumCutLinearArrangement_npComplete :
    minimumCutLinearArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
