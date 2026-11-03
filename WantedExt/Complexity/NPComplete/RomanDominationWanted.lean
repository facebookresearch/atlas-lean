/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROMAN DOMINATION is NP-complete

Source:
E. J. Cockayne, P. A. Dreyer Jr., S. M. Hedetniemi, and S. T. Hedetniemi, "Roman domination in
graphs", Discrete Mathematics 278 (2004), 11-22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RomanDomination

/-!
# ROMAN DOMINATION is NP-complete

An undirected graph and a bound `K`. The question is whether there is a Roman dominating
function: a labeling with values `0, 1, 2` such that every `0`-vertex has a `2`-neighbor, and
the total label weight is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Roman domination instances.** An instance of ROMAN DOMINATION is a triple $(n, E, K)$ of a
natural number $n$, the number of vertices, a list $E$ of pairs of natural numbers, the edges,
and a natural number $K$, the weight bound. -/
abbrev RomanDominationInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a Roman domination instance.** For an instance $(n, E, K)$ of ROMAN DOMINATION,
its graph is the graph of the edge list $E$ on $n$ vertices: the simple graph on
$\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or
$(j, i)$ belongs to $E$. -/
def Graph (i : RomanDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed Roman domination instances.** An instance $(n, E, K)$ of ROMAN DOMINATION is
well formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ has
$u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : RomanDominationInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible Roman domination instances.** An instance $(n, E, K)$ of ROMAN DOMINATION is
feasible when there is a function $f$ from the vertices $\{0, \dots, n - 1\}$ of its graph to
$\{0, 1, 2\}$ such that every vertex $v$ with $f(v) = 0$ is adjacent to some vertex $u$ with
$f(u) = 2$, and the total weight $\sum_v f(v)$ is at most $K$. -/
def RomanDominationFeasible
    (i : RomanDominationInstance) : Prop :=
  ∃ labeling : Fin i.1 → ℕ, (∀ v, labeling v ≤ 2) ∧
    (∀ v, labeling v = 0 → ∃ u, (Graph i).Adj u v ∧ labeling u = 2) ∧
    (Finset.univ.sum labeling) ≤ i.2.2

open Classical in
/-- **ROMAN DOMINATION as a decision problem.** The decision problem ROMAN DOMINATION accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an instance
$(n, E, K)$ of ROMAN DOMINATION that is well formed and feasible; it rejects every other
bitstring. -/
noncomputable def romanDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RomanDominationInstance) x with
  | some i => decide (WellFormed i ∧ RomanDominationFeasible i)
  | none => false

/-- **ROMAN DOMINATION is NP-complete.** The decision problem ROMAN DOMINATION belongs to NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: E. J. Cockayne, P. A. Dreyer Jr., S. M.
Hedetniemi, and S. T. Hedetniemi, "Roman domination in graphs", Discrete Mathematics 278
(2004), 11-22. -/
public theorem_wanted romanDomination_npComplete :
    romanDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L romanDominationDec

end MetaMathlibExt.Complexity.NPComplete.RomanDomination
