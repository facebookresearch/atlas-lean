/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM MULTI-CUT, citing N. Garg, V. V. Vazirani and M. Yannakakis, "Approximate
max-flow min-(multi)cut theorems and their applications", SIAM Journal on Computing 25(2)
(1996), 235-251, doi:10.1137/S0097539793243016;
E. Dahlhaus, D. S. Johnson, C. H. Papadimitriou, P. D. Seymour and M. Yannakakis, "The
complexity of multiterminal cuts", SIAM Journal on Computing 23(4) (1994), 864-894,
doi:10.1137/S0097539792225297 (MULTIWAY CUT, the special case in which `S` consists of all
pairs of `k` terminals, is NP-hard already for `k = 3`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiCut

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), weighted edge list `(u, v, w(e))`,
the list of source-terminal pairs `S`, and the bound `K`. -/
abbrev MultiCutInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The unweighted graph on `Fin n` of a list of weighted edges. -/
def Graph (i : MultiCutInstance) (T : List (ℕ × ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (T.map fun e => (e.1, e.2.1))

/-- Well-formedness of an instance: the edge list has no duplicates, no self-loops, endpoints
below `n`, and at most one edge per unordered vertex pair; every pair of `S` has both vertices
below `n`; and `K` is positive. -/
def WellFormed (i : MultiCutInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1 ∧ p.2 < i.1) ∧ 0 < i.2.2.2

/-- A multi-cut of weight at most `K`: a sublist `E'` of the edges, of total weight at most `K`,
such that after deleting the edges of `E'` from `G` (`SimpleGraph.deleteEdges`) the terminal
of every pair of `S` is not reachable from its source. -/
def MultiCutFeasible (i : MultiCutInstance) : Prop :=
  ∃ C : List (ℕ × ℕ × ℕ), C.Sublist i.2.1 ∧ (C.map fun e => e.2.2).sum ≤ i.2.2.2 ∧
    ∀ p ∈ i.2.2.1, ∀ hs : p.1 < i.1, ∀ ht : p.2 < i.1,
      ¬ ((Graph i i.2.1).deleteEdges (Graph i C).edgeSet).Reachable ⟨p.1, hs⟩ ⟨p.2, ht⟩

open Classical in
/-- MULTI-CUT as a decision problem over bitstrings. -/
noncomputable def multiCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiCut
