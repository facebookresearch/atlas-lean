/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 756
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Geometry.Metric

@[expose] public section

open Filter
open scoped Asymptotics

namespace MathlibExt.Geometry.ErdosProblem756Wanted

/-! Source record `FC-ErdosProblem756`, ported from FormalConjectures
`ErdosProblems/756.lean` and checked against erdosproblems.com/756.
The plane is `EuclideanSpace ℝ (Fin 2)`. The distance API
(`distanceSet`, `distanceMultiplicity`) is reused from `MathlibExt.Geometry.Metric`. The upstream
`answer(True)` is dropped. Status: resolved true by [Bh24]. This module
states the externally proved results but does not prove them; an external
Lean proof is linked in the registry. -/

/-- **Rich distances.** For a finite set $A$ of points in the Euclidean plane and a natural number
$k$, the rich distances of $A$ at level $k$ are the distances $d$ between two distinct points of
$A$ such that at least $k$ unordered pairs of distinct points of $A$ are at distance $d$. -/
noncomputable def richDistances (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) : Finset ℝ :=
  (distanceSet A).filter fun d => k ≤ distanceMultiplicity A d

/-- **Maximal number of rich distances.** For a natural number $n$, this is the largest, over all
sets $A$ of $n$ points in the Euclidean plane, of the number of rich distances of $A$ at level
$n + 1$, that is, of distances that occur for at least $n + 1$ unordered pairs of distinct points
of $A$. -/
noncomputable def maxRichDistances (n : ℕ) : ℕ :=
  sSup {(richDistances A (n + 1)).card | (A : Finset (EuclideanSpace ℝ (Fin 2))) (_ : A.card = n)}

/-- **Statement of Erdős Problem 756 on rich distances.** For a finite set $A$ of points in the
Euclidean plane, call a distance $k$-rich for $A$ if at least $k$ unordered pairs of distinct points
of $A$ lie at that distance, and let $f(n)$ be the largest number of $(n+1)$-rich distances of a
set of $n$ points. This is the assertion that there is a constant $C$ with $n \le C f(n)$ for all
sufficiently large $n$; that for every $n$ there is a set of $n$ points with at least
$\lfloor n/4 \rfloor$ distances that are $(n+1)$-rich; and that for every $m \ge 1$ there is an
$N$ such that for every $n \ge N$ there is a set of $n$ points with at least
$\lfloor n/(2(m+1)) \rfloor$ distances that are $(n+m)$-rich. -/
def conjecture : Prop :=
  ((fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (maxRichDistances n : ℝ))) ∧
  (∀ n : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / 4 ≤ (richDistances A (n + 1)).card) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ᶠ n : ℕ in atTop, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ n / (2 * (m + 1)) ≤ (richDistances A (n + m)).card)

/--
**Bhowmick's theorem on rich distances.** For a finite set $A$ of points in the Euclidean plane,
call a distance $k$-rich for $A$ if at least $k$ unordered pairs of distinct points of $A$ lie at
that distance, and let $f(n)$ be the largest number of $(n+1)$-rich distances of a set of $n$
points. Then there is a constant $C$ with $n \le C f(n)$ for all sufficiently large $n$; for every
$n$ there is a set of $n$ points with at least $\lfloor n/4 \rfloor$ distances that are
$(n+1)$-rich; and for every $m \ge 1$ there is an $N$ such that for every $n \ge N$ there is a set
of $n$ points with at least $\lfloor n/(2(m+1)) \rfloor$ distances that are $(n+m)$-rich.

Source: K. Bhowmick, A problem of Erdős
about rich distances, arXiv:2407.01174 (2024), https://arxiv.org/abs/2407.01174; External Lean
proof of Erdős Problem 756,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos756.lean.
Moved from `OpenConjectures/Geometry/ErdosProblem756`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem756Wanted
