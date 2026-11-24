/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-2090-021`
# Connectivity of non-negative points through non-negative lines in weighted rank-3 matroids

Discrete Geometry (2009), Oberwolfach Reports, DOI 10.4171/owr/2008/44, pp. 2477--2556.
-/
module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Closure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted

/-- **Simple matroid.** A matroid $M$ on elements of $\{0, \dots, n-1\}$ is simple when the set
$\{e, f\}$ is independent in $M$ for all $e, f \in \{0, \dots, n-1\}$, so that every set of at most
two of these elements is independent (no loops, no parallel pairs). -/
def IsSimpleMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop := ∀ e f, M.Indep {e, f}

/-- **Line of a matroid.** A set $L$ of points is a line of a matroid $M$ on elements of
$\{0, \dots, n-1\}$ when $L$ is a flat of $M$ of rank $2$. -/
def IsLine {n : ℕ} (M : Matroid (Fin n)) (L : Set (Fin n)) : Prop := M.IsFlat L ∧ M.eRk L = 2

open Classical in
/-- **Weight of a set of points.** Given real weights $a_0, \dots, a_{n-1}$ on the points
$0, \dots, n-1$, the weight of a set $S$ of points is $\sum_{i \in S} a_i$. -/
noncomputable def weight {n : ℕ} (a : Fin n → ℝ) (S : Set (Fin n)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ∈ S), a i

open Classical in
/-- **Graph of non-negative lines.** Let $M$ be a matroid on elements of $\{0, \dots, n-1\}$ and
let $a_0, \dots, a_{n-1}$ be real weights, the weight of a set of points being the sum of the
weights of its points. The graph of non-negative lines has as vertices the points $i$ with
$a_i \ge 0$, and two distinct vertices are adjacent when some line of $M$ (a flat of rank $2$)
contains both and has non-negative weight. -/
def nonnegGraph {n : ℕ} (M : Matroid (Fin n)) (a : Fin n → ℝ) :
    SimpleGraph {i : Fin n // 0 ≤ a i} :=
  SimpleGraph.fromRel fun i j =>
    ∃ L, IsLine M L ∧ 0 ≤ weight a L ∧ (i : Fin n) ∈ L ∧ (j : Fin n) ∈ L

/-- **Connectivity question for weighted rank-3 matroids.** This is the statement that for every
$n$, every simple matroid $M$ of rank $3$ on the ground set $\{0, \dots, n-1\}$ (every set of at
most two points is independent) and all real weights $a_0, \dots, a_{n-1}$ with
$a_0 + \dots + a_{n-1} \ge 0$, the graph on the points $i$ with $a_i \ge 0$, in which two distinct
points are adjacent when some line of $M$ (a flat of rank $2$) contains both and has non-negative
weight, the weight of a set being the sum of the weights of its points, is connected. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)) (a : Fin n → ℝ), IsSimpleMatroid M → M.eRank = 3 →
    M.E = Set.univ →
    0 ≤ ∑ i, a i → (nonnegGraph M a).Connected

-- Carried source audit `OWR-2090-021` (see the Moved/ record).

/--
**Non-negative points of a weighted rank-3 matroid are connected by non-negative lines.** Let $n$
be a natural number, let $M$ be a simple matroid of rank $3$ on the ground set $\{0, \dots, n-1\}$
(every set of at most two points is independent) and let $a_0, \dots, a_{n-1}$ be real weights
with $a_0 + \dots + a_{n-1} \ge 0$. Then the graph on the points $i$ with $a_i \ge 0$, in which two
distinct points are adjacent when some line of $M$ (a flat of rank $2$) contains both and has
non-negative weight, the weight of a set being the sum of the weights of its points, is
connected.

Resolved true: for a matroid of rank $r$, a generic weight and a threshold $t \le \min\{0, w\}$,
where $w$ is the total weight, the proper flats of weight greater than $t$ form an
$(r - 3)$-connected poset (Adiprasito–Björner, Theorem 2.1, settling the Mikhalkin–Ziegler
conjecture); for $r = 3$, a small generic perturbation with $t$ slightly below $0$ gives the
connectivity of the non-negative points through non-negative lines. Shellability in the omitted
rank-$r$ part is open (their Open Problem 3.2).

Source: K. A. Adiprasito, A. Björner, Filtered geometric lattices and
Lefschetz section theorems over the tropical semiring, arXiv:1401.7301,
https://arxiv.org/abs/1401.7301. Moved from
`OpenConjectures/Combinatorics/WeightedMatroidNonnegativeLinesConnected`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted
