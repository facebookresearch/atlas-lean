/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
# Erdős Problem 755
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open Filter
open scoped Asymptotics EuclideanGeometry Finset

namespace MathlibExt.Geometry.ErdosProblem755Wanted

/-! Source record `FC-ErdosProblem755`, ported from FormalConjectures
`ErdosProblems/755.lean` and checked against erdosproblems.com/755.
The equilateral-triangle counting API is inlined from FC
(`IsEquilateralTriangle`, `IsUnitEquilateralTriangle`,
`IsAnySizeEquilateralTriangle`, `unitEquilateralTriangleCount`,
`anySizeEquilateralTriangleCount`, `TUnit`, `TAnySize`; absent from
pinned Mathlib). `test` lemmas are not ported. The upstream
`answer(True)` is dropped. Status: resolved true by [CDL25b]. This module
states the result but does not prove it; an external Lean proof is linked in
the registry. -/

/-- **Equilateral triangle with given side.** For a real number $s$, a finite set $T$ of
points in the Euclidean space $\mathbb{R}^d$ is an equilateral triangle of side $s$ when $T$ has
exactly three elements and any two distinct points of $T$ are at distance $s$. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- **Unit equilateral triangle.** A finite set $T$ of points in the Euclidean space $\mathbb{R}^d$
is a unit equilateral triangle when it is an equilateral triangle of side $1$: $T$ has exactly
three elements and any two distinct points of $T$ are at distance $1$. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- **Equilateral triangle of any size.** A finite set $T$ of points in the Euclidean space
$\mathbb{R}^d$ is an equilateral triangle of any size when there is a real number $s > 0$ such
that $T$ is an equilateral triangle of side $s$: $T$ has exactly three elements and any two
distinct points of $T$ are at distance $s$. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- **Number of unit equilateral triangles in a point set.** For a finite set $P$ of points in
the Euclidean space $\mathbb{R}^d$, this is the number of three-element subsets of $P$ that are
unit equilateral triangles, that is, whose three points are pairwise at distance $1$. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- **Number of equilateral triangles in a point set.** For a finite set $P$ of points in the
Euclidean space $\mathbb{R}^d$, this is the number of three-element subsets of $P$ that are
equilateral triangles of some positive side length $s$, that is, whose three points are pairwise
at distance $s$. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- **Maximum number of unit equilateral triangles.** For natural numbers $d$ and $n$, $T_1(d, n)$
is the supremum in $\mathbb{N}$, over all sets $P$ of exactly $n$ points in the Euclidean space
$\mathbb{R}^d$, of the number of unit equilateral triangles spanned by $P$ (the three-element
subsets of $P$ whose points are pairwise at distance $1$). When such sets exist this is the
largest such number; when none exist (only for $d = 0$ and $n \ge 2$) it is $0$. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- **Maximum number of equilateral triangles.** For natural numbers $d$ and $n$, $T(d, n)$ is the
supremum in $\mathbb{N}$, over all sets $P$ of exactly $n$ points in the Euclidean space
$\mathbb{R}^d$, of the number of equilateral triangles of positive side length spanned by $P$
(the three-element subsets of $P$ whose points are pairwise at the same positive distance). When
such sets exist this is the largest such number; when none exist (only for $d = 0$ and $n \ge 2$)
it is $0$. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

/-- **Statement of Erdős Problem 755.** Let $T_1(n)$ be the largest number of unit equilateral
triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the largest number
of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. The statement asserts both of the following: there is a function
$o : \mathbb{N} \to \mathbb{R}$ with $o(n) \to 0$ as $n \to \infty$ such that
$T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently large $n$; and $T(n)$ is asymptotically
equivalent to $n^3/27$ as $n \to \infty$. -/
def conjecture : Prop :=
  (∃ o : ℕ → ℝ,
    o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n in atTop,
        (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3) ∧
  ((fun n : ℕ => (TAnySize 6 n : ℝ)) ~[atTop]
    (fun n : ℕ => (1 / 27 : ℝ) * (n : ℝ) ^ 3))

/--
**Erdős Problem 755 holds (Clemen–Dumitrescu–Liu).** Let $T_1(n)$ be the largest number of unit
equilateral triangles spanned by a set of $n$ points in $\mathbb{R}^6$, and let $T(n)$ be the
largest number of equilateral triangles of positive side length spanned by a set of $n$ points in
$\mathbb{R}^6$; a triangle spanned by a set is a three-element subset of it whose points are
pairwise at the same distance. Then there is a function $o : \mathbb{N} \to \mathbb{R}$ with
$o(n) \to 0$ as $n \to \infty$ such that $T_1(n) \le (1/27 + o(n))\, n^3$ for all sufficiently
large $n$, and $T(n)$ is asymptotically equivalent to $n^3/27$ as $n \to \infty$.

Source: Felix
Christian Clemen, Adrian Dumitrescu, and Dingyuan Liu, The number of regular simplices in higher
dimensions, arXiv:2507.19841 (2025), https://arxiv.org/abs/2507.19841. Moved from
`OpenConjectures/Geometry/ErdosProblem755`. Resolved true: Resolved externally by Clemen,
Dumitrescu, and Liu. This repository records the statement, not an internal proof; a separate
pinned Lean proof is cited in the registry.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem755Wanted
