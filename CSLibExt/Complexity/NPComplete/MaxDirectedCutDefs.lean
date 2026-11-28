/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX DIRECTED CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MAXIMUM DIRECTED CUT (decision version);
J. Håstad, "Some optimal inapproximability results", Journal of the ACM 48(4) (2001),
798-859, doi:10.1145/502090.502098 (Definition 2.7 and Theorem 8.3 in the author's
version);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1
(SIMPLE MAX CUT; M. R. Garey and D. S. Johnson, *Computers and Intractability*, W. H. Freeman
(1979), problem [ND16], comment).
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxDirectedCut

/-- An instance: vertex count `n` (vertices `Fin n`), arc list, and the bound `K`. -/
abbrev MaxDirectedCutInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph `G = (V, A)` of the instance: an arc from `u` to `v` when `(u, v)` is
listed. -/
def Graph (i : MaxDirectedCutInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs, no loops, and endpoints
in range, and `K` is positive. -/
def WellFormed (i : MaxDirectedCutInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧ 0 < i.2.2

open Classical in
/-- The number of arcs of `G` with start point in `V₁` and endpoint outside `V₁`. -/
noncomputable def cutSize (i : MaxDirectedCutInstance) (V₁ : Finset (Fin i.1)) : ℕ :=
  (Finset.univ.filter fun p : Fin i.1 × Fin i.1 =>
    (Graph i).Adj p.1 p.2 ∧ p.1 ∈ V₁ ∧ p.2 ∉ V₁).card

/-- Some partition of `V` into `V₁` and `V₂ = V \ V₁` has at least `K` arcs from `V₁` to
`V₂`. -/
def MaxDirectedCutFeasible (i : MaxDirectedCutInstance) : Prop :=
  ∃ V₁ : Finset (Fin i.1), i.2.2 ≤ cutSize i V₁

open Classical in
/-- MAX DIRECTED CUT as a decision problem over bitstrings. -/
noncomputable def maxDirectedCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxDirectedCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxDirectedCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxDirectedCut
