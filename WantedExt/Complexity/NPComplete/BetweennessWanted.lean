/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BETWEENNESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BETWEENNESS; M. Opatrny,
"Total ordering problem" (1979).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Betweenness

/-!
# BETWEENNESS is NP-complete

A list of triples of distinct elements. The question is whether there is a total ordering in
which the middle element of every triple lies strictly between the other two.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BETWEENNESS instances.** An instance of BETWEENNESS is a pair $(n, T)$ of a natural number
$n$ (the number of elements) and a list $T$ of triples of natural numbers. -/
abbrev BetweennessInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- **Well-formed BETWEENNESS instances.** A BETWEENNESS instance $(n, T)$ is well formed when
every triple $(a, b, c)$ in $T$ satisfies $a < n$, $b < n$ and $c < n$, and $a$, $b$, $c$ are
pairwise distinct. -/
def WellFormed (i : BetweennessInstance) : Prop :=
  ∀ t ∈ i.2, t.1 < i.1 ∧ t.2.1 < i.1 ∧ t.2.2 < i.1 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- **BETWEENNESS feasibility.** A BETWEENNESS instance $(n, T)$ is feasible when there is an
ordering of the numbers $0, \dots, n-1$ such that for every triple $(a, b, c)$ in $T$, either
$p(a) < p(b) < p(c)$ or $p(c) < p(b) < p(a)$, where $p(m)$ is the position of $m$ in the
ordering, counting from $0$, and $p(m) = n$ when $m$ is not among $0, \dots, n-1$. -/
def BetweennessFeasible
    (i : BetweennessInstance) : Prop :=
  ∃ ord : List ℕ, ord.Perm (List.range i.1) ∧
    ∀ t ∈ i.2, (ord.idxOf t.1 < ord.idxOf t.2.1 ∧ ord.idxOf t.2.1 < ord.idxOf t.2.2) ∨
      (ord.idxOf t.2.2 < ord.idxOf t.2.1 ∧ ord.idxOf t.2.1 < ord.idxOf t.1)

open Classical in
/-- **The BETWEENNESS decision problem.** BETWEENNESS accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of pairs $(n, T)$ of a natural number and a list
of triples of natural numbers, to a BETWEENNESS instance that is both well formed and feasible.
Bitstrings that do not decode to such a pair are rejected. -/
noncomputable def betweennessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BetweennessInstance) x with
  | some i => decide (WellFormed i ∧ BetweennessFeasible i)
  | none => false

/-- **BETWEENNESS is NP-complete.** The BETWEENNESS decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), BETWEENNESS; M. Opatrny, "Total ordering problem" (1979). -/
public theorem_wanted betweenness_npComplete :
    betweennessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L betweennessDec

end MetaMathlibExt.Complexity.NPComplete.Betweenness
