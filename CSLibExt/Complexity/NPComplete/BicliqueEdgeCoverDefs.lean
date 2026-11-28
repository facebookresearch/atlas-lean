/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLIQUE EDGE COVER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BICLIQUE COVER.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover

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

end MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover
