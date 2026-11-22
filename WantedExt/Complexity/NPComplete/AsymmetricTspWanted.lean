/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON
PROBLEM (asymmetric).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp

/-!
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

An integer-weighted complete directed graph, given by a weight matrix with zero diagonal (not
assumed symmetric), and a bound `B`. The question is whether there is a directed tour visiting
every vertex exactly once whose total weight, including the return to the start, is at most
`B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Asymmetric TSP instances.** An instance of the asymmetric traveling salesperson problem is a
triple $(n, w, B)$ consisting of a natural number $n$ (the number of cities), a weight matrix $w$
given as a list of rows, each row a list of natural numbers, and a natural number $B$ (the
bound). -/
abbrev AsymmetricTspInstance := ℕ × List (List ℕ) × ℕ


/-- **Length of a tour in the asymmetric TSP.** Let $w$ be a weight matrix, given as a list of rows
of natural numbers, and let $t = (t_0, \dots, t_{L-1})$ be a list of natural numbers. The length
of the tour $t$ under $w$ is $\sum_{j=0}^{L-1} w_{t_j, t_{(j+1) \bmod L}}$, the sum of the weights
along the closed walk including the return edge from $t_{L-1}$ to $t_0$, where $w_{a,b}$ denotes
the entry in row $a$ and column $b$ of $w$, taken to be $0$ when that entry does not exist. In
particular the empty tour has length $0$. -/
def TourLength (w : List (List ℕ)) (tour : List ℕ) : ℕ :=
  ((List.range tour.length).map (fun j =>
    (w.getD (tour.getD j 0) []).getD (tour.getD ((j + 1) % tour.length) 0) 0)).sum


/-- **Well-formed asymmetric TSP instances.** An asymmetric TSP instance $(n, w, B)$, with $n$ the
number of cities, $w$ the weight matrix and $B$ the bound, is well formed when $n > 0$, $w$ has
exactly $n$ rows, every row of $w$ has length $n$, and the diagonal entry $w_{a,a}$ in row $a$
and column $a$ is $0$ for every $a < n$. -/
def WellFormed (i : AsymmetricTspInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    ∀ a < i.1, (i.2.1.getD a []).getD a 0 = 0

/-- **Feasible asymmetric TSP instances.** An asymmetric TSP instance $(n, w, B)$ is feasible when
there is a list $t$ of natural numbers with no repeated entries, of length $n$ and containing
every $v < n$ (so $t$ lists the cities $0, \dots, n - 1$ in some order), whose tour length under
$w$ is at most $B$. -/
def AsymmetricTspFeasible
    (i : AsymmetricTspInstance) : Prop :=
  ∃ tour : List ℕ, tour.Nodup ∧ tour.length = i.1 ∧ (∀ v < i.1, v ∈ tour) ∧
    TourLength i.2.1 tour ≤ i.2.2

open Classical in
/-- **The asymmetric traveling salesperson decision problem.** The asymmetric TSP decision problem
accepts a bitstring $x$ when $x$ decodes, under the canonical bitstring encoding of asymmetric TSP
instances, to an instance $(n, w, B)$ that is well formed and feasible, and rejects $x$
otherwise; in particular it rejects every bitstring that does not decode to an instance. -/
noncomputable def asymmetricTspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AsymmetricTspInstance) x with
  | some i => decide (WellFormed i ∧ AsymmetricTspFeasible i)
  | none => false

/-- **TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete.** The asymmetric traveling salesperson
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON PROBLEM
(asymmetric). -/
public theorem_wanted asymmetricTsp_npComplete :
    asymmetricTspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L asymmetricTspDec

end MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp
