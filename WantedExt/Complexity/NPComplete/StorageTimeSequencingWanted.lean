/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STORAGE-TIME SEQUENCING is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing

/-!
# STORAGE-TIME SEQUENCING is NP-complete

INSTANCE: a set `T` of tasks, a directed acyclic graph `G = (T, E)` of precedence constraints,
for each task a length `l(t) ∈ Z⁺`, for each edge `⟨t₁, t₂⟩` a weight `w(t₁, t₂)` (the storage
needed to save the intermediate results of `t₁` until `t₂` consumes them), and a positive integer
`K`. QUESTION: is there a one-processor schedule obeying the precedence constraints, i.e. a
permutation `π` of `[1..|T|]` with `π⁻¹(i) < π⁻¹(j)` for every edge `⟨tᵢ, tⱼ⟩ ∈ E`, whose total
storage-time product
`∑_{⟨t_{π(i)}, t_{π(j)}⟩ ∈ E} w(t_{π(i)}, t_{π(j)}) · ∑_{k = min(i,j)}^{max(i,j)} l(t_{π(k)})`
is at most `K`?

The tasks are `0, …, n - 1`, where `n` is the length of the list of task lengths. An edge is a
triple `(t₁, t₂, w)`: the arc `⟨t₁, t₂⟩` with weight `w ∈ ℕ` (the compendium gives no range for
the weights). As in `WantedExt.Complexity.NPComplete.DirectedOptimalLinearArrangementWanted`, a
schedule is a permutation `perm` of `List.range n` listing the tasks in processing order:
position `k` holds task `perm[k]` (the compendium's `π(k + 1)`, positions counted from `0`), and
the position of task `t` is `perm.idxOf t`. The storage of edge `⟨t₁, t₂⟩` is weighted by the
total length of the tasks in positions `min(p₁, p₂), …, max(p₁, p₂)`, where `pᵢ` is the position
of `tᵢ`. Each edge carries one weight, so the edge list has no repeated arc; the digraph is
acyclic.

With unit lengths and unit weights the storage-time product of a schedule is
`∑_{⟨t₁, t₂⟩ ∈ E} (p₂ - p₁ + 1)`, the DIRECTED OPTIMAL LINEAR ARRANGEMENT cost ([GT43]) plus
`|E|`. Membership in NP: the schedule is a certificate, and its storage-time product is computed
in polynomial time. Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **STORAGE-TIME SEQUENCING is NP-complete.** Source: Crescenzi and Kann, MINIMUM
STORAGE-TIME SEQUENCING; Rao and Richa (2005); Garey and Johnson (1979), [GT43] (special case). -/
public theorem_wanted storageTimeSequencing_npComplete :
    storageTimeSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L storageTimeSequencingDec

end MetaMathlibExt.Complexity.NPComplete.StorageTimeSequencing
