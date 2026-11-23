/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D.
G. Corneil and Y. Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-
code literature.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EfficientDomination

/-!
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

An undirected graph. The question is whether the graph has an efficient dominating set (a
perfect code): a set `S` such that every vertex has exactly one closed neighbor in `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Efficient Domination instances.** An instance of EFFICIENT DOMINATION is a pair $(n, E)$
of a natural number $n$, the number of vertices, and a list $E$ of pairs of natural numbers, the
edges. -/
abbrev EfficientDominationInstance := ℕ × List (ℕ × ℕ)

/-- **Graph of an Efficient Domination instance.** For an instance $(n, E)$, its graph is the
simple graph on the vertex set $\{0, \dots, n - 1\}$ in which distinct vertices $u$ and $v$ are
adjacent when $(u, v)$ or $(v, u)$ belongs to $E$. -/
def Graph (i : EfficientDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- **Well-formed Efficient Domination instances.** An instance $(n, E)$ is well formed when the
list $E$ has no repeated entries and every pair $(a, b)$ in $E$ satisfies $a < n$, $b < n$ and
$a \ne b$, and $(b, a)$ does not belong to $E$. -/
def WellFormed (i : EfficientDominationInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- **Instances with an efficient dominating set.** An instance $(n, E)$ of EFFICIENT DOMINATION
is feasible when its graph has an efficient dominating set (a perfect code): a set $S$ of
vertices such that every vertex $v$ has exactly one vertex $u \in S$ with $u = v$ or $u$
adjacent to $v$. -/
def EfficientDominationFeasible
    (i : EfficientDominationInstance) : Prop :=
  ∃ S : Finset (Fin i.1),
    ∀ v : Fin i.1, ∃! u ∈ S, u = v ∨ (Graph i).Adj u v

open Classical in
/-- **EFFICIENT DOMINATION (PERFECT CODE) as a decision problem.** The decision problem
EFFICIENT DOMINATION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of instances, to an instance $(n, E)$ that is well formed and whose graph has
an efficient dominating set. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def efficientDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EfficientDominationInstance) x with
  | some i => decide (WellFormed i ∧ EfficientDominationFeasible i)
  | none => false

/-- **EFFICIENT DOMINATION (PERFECT CODE) is NP-complete.** The decision problem EFFICIENT
DOMINATION belongs to NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D. G. Corneil and Y.
Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-code
literature. -/
public theorem_wanted efficientDomination_npComplete :
    efficientDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L efficientDominationDec

end MetaMathlibExt.Complexity.NPComplete.EfficientDomination
