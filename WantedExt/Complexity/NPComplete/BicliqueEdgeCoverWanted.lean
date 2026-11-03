/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLIQUE EDGE COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BICLIQUE COVER.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover

/-!
# BICLIQUE EDGE COVER is NP-complete

A bipartite graph (left vertices `0, …, L - 1`, right vertices `0, …, R - 1`) and a bound `K`.
The question is whether all edges can be covered by at most `K` complete bipartite subgraphs
(bicliques), each given by a left set and a right set with all cross pairs present as edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Biclique edge cover instances.** An instance of BICLIQUE EDGE COVER is a tuple
$(L, R, E, K)$ of natural numbers $L$, $R$ and $K$ and a finite list $E$ of pairs of natural
numbers. Here $L$ counts the left vertices, $R$ counts the right vertices, each pair $(a, b)$ in
$E$ is an edge from left vertex $a$ to right vertex $b$, and $K$ is the bound on the number of
bicliques. -/
abbrev BicliqueEdgeCoverInstance := ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed biclique edge cover instances.** An instance $(L, R, E, K)$ of BICLIQUE EDGE
COVER is well formed when the list $E$ has no repeated entries and every pair $(a, b)$ in $E$
satisfies $a < L$ and $b < R$. -/
def WellFormed (i : BicliqueEdgeCoverInstance) : Prop :=
  i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.2.1

/-- **Feasible biclique edge cover instances.** An instance $(L, R, E, K)$ of BICLIQUE EDGE
COVER is feasible when there is a list of at most $K$ pairs $(A, B)$ of finite lists of natural
numbers, with every element of $A$ less than $L$ and every element of $B$ less than $R$, such
that for every pair $(u, v)$ in $E$ some listed pair $(A, B)$ has $u \in A$, $v \in B$ and
$(a, b)$ in $E$ for all $a \in A$ and $b \in B$. -/
def BicliqueEdgeCoverFeasible
    (i : BicliqueEdgeCoverInstance) : Prop :=
  ∃ bicliques : List (List ℕ × List ℕ), bicliques.length ≤ i.2.2.2 ∧
    (∀ p ∈ bicliques, (∀ a ∈ p.1, a < i.1) ∧ ∀ b ∈ p.2, b < i.2.1) ∧
    ∀ e ∈ i.2.2.1, ∃ p ∈ bicliques, e.1 ∈ p.1 ∧ e.2 ∈ p.2 ∧
      ∀ a ∈ p.1, ∀ b ∈ p.2, (a, b) ∈ i.2.2.1

open Classical in
/-- **The biclique edge cover decision problem.** BICLIQUE EDGE COVER is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding
of biclique edge cover instances, to an instance that is well formed and feasible; it rejects
every bitstring that fails to decode. -/
noncomputable def bicliqueEdgeCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BicliqueEdgeCoverInstance) x with
  | some i => decide (WellFormed i ∧ BicliqueEdgeCoverFeasible i)
  | none => false

/-- **BICLIQUE EDGE COVER is NP-complete.** The biclique edge cover decision problem belongs to
NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), BICLIQUE COVER. -/
public theorem_wanted bicliqueEdgeCover_npComplete :
    bicliqueEdgeCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bicliqueEdgeCoverDec

end MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover
