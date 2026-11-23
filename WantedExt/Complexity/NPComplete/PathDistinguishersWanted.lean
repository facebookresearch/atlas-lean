/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH DISTINGUISHERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT60] PATH DISTINGUISHERS;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Report CU-CS-092-76,
Department of Computer Science, University of Colorado, Boulder (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathDistinguishers

/-!
# PATH DISTINGUISHERS is NP-complete

Given an acyclic directed graph `G = (V, A)`, specified vertices `s, t ∈ V`, and a positive
integer `K ≤ |A|`, is there a subset `A' ⊆ A` with `|A'| ≤ K` such that, for any pair `p₁, p₂`
of directed paths from `s` to `t` in `G`, `p₁` and `p₂` are identical if and only if they
contain the same arcs of `A'`?

The digraph has vertices `Fin n` and is given by its arc list, with no loops and no multiple
arcs; acyclicity (no vertex reaches itself by a nonempty sequence of arcs) is part of
`WellFormed`. A directed path from `s` to `t` is a list of vertices without repetitions that
starts at `s`, ends at `t`, and has an arc from each vertex to the next; its arcs are the
consecutive pairs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, arc list `A` (pairs `(u, v)` for arcs `u → v`), source `s`,
target `t`, and the bound `K`. -/
abbrev PathDistinguishersInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The digraph of the instance on `Fin n`: `u → v` is an arc iff `(u, v)` is in the arc
list. -/
def Graph (i : PathDistinguishersInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- `p` is a directed path from `s` to `t` in `G`: its first vertex is `s`, its last vertex is
`t`, it repeats no vertex, and each vertex has an arc to the next. -/
def IsPath {n : ℕ} (G : Digraph (Fin n)) (s t : ℕ) (p : List (Fin n)) : Prop :=
  (p.map Fin.val).head? = some s ∧ (p.map Fin.val).getLast? = some t ∧ p.Nodup ∧
    p.IsChain G.Adj

/-- The arcs of a vertex sequence: the pairs of consecutive vertices. -/
def pathArcs {n : ℕ} (p : List (Fin n)) : List (Fin n × Fin n) :=
  p.zip p.tail

/-- Well-formedness of an instance: the arc list has no repeated arcs, its endpoints are
vertices, and it has no loops; the digraph is acyclic; `s` and `t` are vertices; and
`0 < K ≤ |A|`. -/
def WellFormed (i : PathDistinguishersInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2 ∧ i.2.2.2.2 ≤ i.2.1.length

/-- A set `A'` of at most `K` arcs such that two `s`-`t` paths are identical iff they contain
the same arcs of `A'`. -/
def PathDistinguishersFeasible (i : PathDistinguishersInstance) : Prop :=
  ∃ A' : Finset (Fin i.1 × Fin i.1), (∀ a ∈ A', (Graph i).Adj a.1 a.2) ∧
    A'.card ≤ i.2.2.2.2 ∧
    ∀ p q, IsPath (Graph i) i.2.2.1 i.2.2.2.1 p → IsPath (Graph i) i.2.2.1 i.2.2.2.1 q →
      (p = q ↔ ∀ a ∈ A', (a ∈ pathArcs p ↔ a ∈ pathArcs q))

open Classical in
/-- PATH DISTINGUISHERS as a decision problem over bitstrings. -/
noncomputable def pathDistinguishersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathDistinguishersInstance) x with
  | some i => decide (WellFormed i ∧ PathDistinguishersFeasible i)
  | none => false

/-- **PATH DISTINGUISHERS is NP-complete.** Source: Garey and Johnson (1979), [GT60];
Maheshwari (1976). -/
public theorem_wanted pathDistinguishers_npComplete :
    pathDistinguishersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathDistinguishersDec

end MetaMathlibExt.Complexity.NPComplete.PathDistinguishers
