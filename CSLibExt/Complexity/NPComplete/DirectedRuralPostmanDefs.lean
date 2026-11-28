/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED RURAL POSTMAN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN, comment on
p. 213 ("as does the corresponding problem for directed graphs");
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976),
273-280, doi:10.1002/net.3230060305, Theorem (p. 275: the rural postman problem is
NP-complete "both in the case that G is undirected and in the case that G is directed").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman

/-- An instance: vertex count `n`, the arcs `(u, v, l)` (from `u` to `v`, length `l`), the
required arcs `A'` as pairs `(u, v)`, and the bound `B`. -/
abbrev DirectedRuralPostmanInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The arc with index `j` (a default triple for an index out of range). -/
def arc (i : DirectedRuralPostmanInstance) (j : ℕ) : ℕ × ℕ × ℕ :=
  i.2.1.getD j (0, 0, 0)

/-- Well-formedness of an instance: the graph has a vertex (`0 < n`), every arc joins two
distinct vertices below `n`, no two arcs have the same tail and head, every required pair is the
pair of an arc, and `0 < B`. -/
def WellFormed (i : DirectedRuralPostmanInstance) : Prop :=
  0 < i.1 ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1) ∧
    (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ r ∈ i.2.2.1, r ∈ i.2.1.map fun a => (a.1, a.2.1)) ∧ 0 < i.2.2.2

/-- Some closed directed walk, given as a list of arc indices, traverses every required arc and
has total length at most `B` (each traversal of an arc counts its length). -/
def DirectedRuralPostmanFeasible (i : DirectedRuralPostmanInstance) : Prop :=
  ∃ walk : List ℕ, (∀ j ∈ walk, j < i.2.1.length) ∧
    walk.IsChain (fun j k => (arc i j).2.1 = (arc i k).1) ∧
    walk.getLast?.map (fun j => (arc i j).2.1) = walk.head?.map (fun j => (arc i j).1) ∧
    (∀ r ∈ i.2.2.1, ∃ j ∈ walk, ((arc i j).1, (arc i j).2.1) = r) ∧
    (walk.map fun j => (arc i j).2.2).sum ≤ i.2.2.2

open Classical in
/-- DIRECTED RURAL POSTMAN as a decision problem over bitstrings. -/
noncomputable def directedRuralPostmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedRuralPostmanInstance) x with
  | some i => decide (WellFormed i ∧ DirectedRuralPostmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman
