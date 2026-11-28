/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list, bound `K`. -/
abbrev MinimumCutLinearArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, ..., n - 1`
(no duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- A one-to-one numbering of the vertices, given by the positions in a permutation `perm` of
`0, ..., n - 1`, such that for every cut position `j` with `j + 1 < n` at most `K` entries
`(u, v)` of the edge list have one endpoint at a position `≤ j` and the other at a position
`> j`; a vertex not in `perm` has position `n`. Entries are counted, so `(0, 1)` and `(1, 0)`
count twice; on a simple edge list, which well-formedness checks, this counts edges. -/
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

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
