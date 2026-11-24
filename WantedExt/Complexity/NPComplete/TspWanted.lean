/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESPERSON (SYMMETRIC) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON
PROBLEM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tsp

/-!
# TRAVELING SALESPERSON (SYMMETRIC) is NP-complete

A symmetric integer-weighted complete graph, given by a symmetric weight matrix with zero
diagonal, and a bound `B`. The question is whether there is a tour visiting every vertex
exactly once whose total weight, including the return to the start, is at most `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Symmetric TSP instances.** An instance of the symmetric traveling salesperson problem is a
triple $(n, w, B)$ of a natural number $n$, the number of cities, a weight matrix $w$ given as a
finite list of rows, each a finite list of natural numbers, and a natural number $B$, the bound.

The type itself does not require $w$ to be an $n \times n$ symmetric matrix with zero diagonal. -/
abbrev TspInstance := ℕ × List (List ℕ) × ℕ


/-- **Length of a tour in the symmetric TSP.** Let $w$ be a matrix of natural numbers given as a
list of rows, where an entry $w_{a,b}$ outside the list (no row $a$, or row $a$ too short) is
read as $0$, and rows and columns are numbered from $0$. The length of a list
$(t_0, \dots, t_{k-1})$ of natural numbers with respect to $w$ is
$\sum_{j<k} w_{t_j, t_{(j+1) \bmod k}}$, the total weight of the edges along the cycle
$t_0, t_1, \dots, t_{k-1}, t_0$, including the return edge; the empty list has length $0$. -/
def TourLength (w : List (List ℕ)) (tour : List ℕ) : ℕ :=
  ((List.range tour.length).map (fun j =>
    (w.getD (tour.getD j 0) []).getD (tour.getD ((j + 1) % tour.length) 0) 0)).sum


/-- **Well-formed symmetric TSP instances.** A symmetric TSP instance $(n, w, B)$ is well formed
when $n > 0$, the weight matrix $w$ has exactly $n$ rows and each row has exactly $n$ entries, $w$
is symmetric, that is $w_{a,b} = w_{b,a}$ for all $a, b < n$, and $w$ has zero diagonal, that is
$w_{a,a} = 0$ for all $a < n$. Rows and columns are numbered from $0$. -/
def WellFormed (i : TspInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ a < i.1, ∀ b < i.1, (i.2.1.getD a []).getD b 0 = (i.2.1.getD b []).getD a 0) ∧
    ∀ a < i.1, (i.2.1.getD a []).getD a 0 = 0

/-- **Feasible symmetric TSP instances.** A symmetric TSP instance $(n, w, B)$ is feasible when
there is a list of $n$ pairwise distinct natural numbers containing every $v < n$, that is, an
ordering of the cities $0, 1, \dots, n-1$ visiting each exactly once, whose tour length with
respect to $w$ (the sum of the weights of consecutive edges, including the return edge) is at
most $B$. -/
def TspFeasible
    (i : TspInstance) : Prop :=
  ∃ tour : List ℕ, tour.Nodup ∧ tour.length = i.1 ∧ (∀ v < i.1, v ∈ tour) ∧
    TourLength i.2.1 tour ≤ i.2.2

open Classical in
/-- **Symmetric TSP as a decision problem.** The symmetric traveling salesperson problem is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of symmetric TSP instances, to an instance $(n, w, B)$ that is well formed and
feasible. Bitstrings that fail to decode, and bitstrings that decode to instances that are not
well formed, are rejected. -/
noncomputable def tspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspInstance) x with
  | some i => decide (WellFormed i ∧ TspFeasible i)
  | none => false

/-- **TRAVELING SALESPERSON (SYMMETRIC) is NP-complete.** The symmetric traveling salesperson
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON PROBLEM. -/
public theorem_wanted tsp_npComplete :
    tspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tspDec

end MetaMathlibExt.Complexity.NPComplete.Tsp
