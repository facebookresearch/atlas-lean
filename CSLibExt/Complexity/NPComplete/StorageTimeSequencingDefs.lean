/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STORAGE-TIME SEQUENCING: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MINIMUM
STORAGE-TIME SEQUENCING (the instance, schedule and storage-time measure);
S. Rao and A. W. Richa, "New approximation techniques for some linear ordering problems", SIAM
Journal on Computing 34(2) (2005), 388-404, doi:10.1137/S0097539702413197 (records minimum
storage-time product as NP-hard);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT43] DIRECTED OPTIMAL LINEAR ARRANGEMENT
(the special case of unit lengths and weights, up to the additive constant `|E|`).
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing

/-- An instance: the task lengths `l(0), …, l(n - 1)`, the edges `(t₁, t₂, w)` (arc `⟨t₁, t₂⟩`
with weight `w`), and the bound `K`. -/
abbrev StorageTimeSequencingInstance := List ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The precedence digraph on the tasks `Fin n`: an arc `⟨t₁, t₂⟩` for every edge. -/
def Graph (i : StorageTimeSequencingInstance) : Digraph (Fin i.1.length) where
  Adj u v := ∃ e ∈ i.2.1, e.1 = u ∧ e.2.1 = v

/-- Well-formedness of an instance: every length is positive, every edge joins two tasks, no
arc carries two weights (the arcs of the edge list are distinct), the precedence digraph is
acyclic (no task reaches itself by a nonempty directed path), and `K` is positive. -/
def WellFormed (i : StorageTimeSequencingInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x) ∧ (∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2.1 < i.1.length) ∧
    (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ 0 < i.2.2

/-- The total storage-time product of the processing order `perm`: for each edge
`(t₁, t₂, w)`, the weight `w` times the total length of the tasks in the positions from
`min(p₁, p₂)` to `max(p₁, p₂)`. -/
def storageTime (i : StorageTimeSequencingInstance) (perm : List ℕ) : ℕ :=
  (i.2.1.map fun e => e.2.2 *
    ∑ k ∈ Finset.Icc (min (perm.idxOf e.1) (perm.idxOf e.2.1))
      (max (perm.idxOf e.1) (perm.idxOf e.2.1)), i.1.getD (perm.getD k 0) 0).sum

/-- Some processing order of the tasks obeys every precedence constraint and has storage-time
product at most `K`. -/
def StorageTimeSequencingFeasible (i : StorageTimeSequencingInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1.length) ∧
    (∀ e ∈ i.2.1, perm.idxOf e.1 < perm.idxOf e.2.1) ∧ storageTime i perm ≤ i.2.2

open Classical in
/-- STORAGE-TIME SEQUENCING as a decision problem over bitstrings. -/
noncomputable def storageTimeSequencingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StorageTimeSequencingInstance) x with
  | some i => decide (WellFormed i ∧ StorageTimeSequencingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing
