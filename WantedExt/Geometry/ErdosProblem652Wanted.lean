/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 652
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.ErdosProblem652Wanted

/-! Source record `EP-652` (Erdős Problem 652). -/

/-- **Euclidean plane for Erdős Problem 652.** The real Euclidean plane is the space
$\mathbb{R}^2$ of pairs of real numbers with the Euclidean inner product and norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Points with few distinct distances.** For a finite set $X$ of points in the Euclidean plane
and a real number $t$, the number of points $x \in X$ such that the number of distinct distances
from $x$ to the other points of $X$ is less than $t$. -/
noncomputable def countSmallPoints (X : Finset Plane) (threshold : ℝ) : ℕ := by
  classical
  exact (X.filter (fun x => (distinctDistancesFrom X x : ℝ) < threshold)).card

/-- **Many points with few distinct distances.** For natural numbers $n$, $k$ and a real number
$c$, the property that some set $X$ of exactly $n$ points in the Euclidean plane contains at
least $k$ points $x$ such that the number of distinct distances from $x$ to the other points of
$X$ is less than $c\sqrt{n}$.

For $1 \le k \le n$ this says that, with the points of $X$ ordered by this number, the $k$-th
smallest value is less than $c\sqrt{n}$. -/
def HasSmallKth (n k : ℕ) (bound : ℝ) : Prop :=
  ∃ X : Finset Plane, X.card = n ∧
    k ≤ countSmallPoints X (bound * Real.sqrt (n : ℝ))

/-- **Admissible constants in Erdős Problem 652.** A real number $c$ is admissible for
$k \in \mathbb{N}$ if there is $N$ such that for every $n \ge N$ some set $X$ of exactly $n$
points in the Euclidean plane contains at least $k$ points $x$ such that the number of distinct
distances from $x$ to the other points of $X$ is less than $c\sqrt{n}$. -/
def isAdmissibleBound (k : ℕ) (bound : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasSmallKth n k bound

/-- **The Erdős constant $\alpha_k$.** For $k \in \mathbb{N}$, $\alpha_k$ is the infimum of the
set of real numbers that are admissible for $k$: the reals $c$ for which there is $N$ such
that for every $n \ge N$ some set $X$ of exactly $n$ points in the Euclidean plane contains
at least $k$ points $x$ such that the number of distinct distances from $x$ to the other points
of $X$ is less than $c\sqrt{n}$. If this set is empty or unbounded below, $\alpha_k = 0$. -/
noncomputable def erdosAlpha (k : ℕ) : ℝ :=
  sInf { bound : ℝ | isAdmissibleBound k bound }

/-- **Erdős Problem 652.** For a finite set $X$ of points in the Euclidean plane and $x \in X$,
let $R_X(x)$ be the number of distinct distances from $x$ to the other points of $X$. For
$k \in \mathbb{N}$ let $\alpha_k$ be the infimum of the reals $c$ for which there is $N$ such
that for every $n \ge N$ some set $X$ of exactly $n$ points in the plane has at least $k$
points $x$ with $R_X(x) < c\sqrt{n}$ (an empty set or a set unbounded below is given infimum
$0$). The proposition is that $\alpha_k \to \infty$ as $k \to \infty$. -/
def conjecture : Prop :=
  Filter.Tendsto erdosAlpha Filter.atTop Filter.atTop

/--
**Erdős Problem 652 is true.** For a finite set $X$ of points in the Euclidean plane and
$x \in X$, let $R_X(x)$ be the number of distinct distances from $x$ to the other points of
$X$. For $k \in \mathbb{N}$ let $\alpha_k$ be the infimum of the reals $c$ for which there is
$N$ such that for every $n \ge N$ some set $X$ of exactly $n$ points in the plane has at least
$k$ points $x$ with $R_X(x) < c\sqrt{n}$ (an empty set or a set unbounded below is given
infimum $0$). Then $\alpha_k \to \infty$ as $k \to \infty$.

Mathialagan proved that for $2 \le m \le n^{1/3}$, some point of an $m$-point set determines
$\Omega(\sqrt{mn})$ distances to an $n$-point set; with Elekes's circle-grid construction this
gives $\alpha_k = \Theta(\sqrt{k})$.

Source: S. Mathialagan, On bipartite distinct distances in the plane,
Electronic Journal of Combinatorics 28(4) (2021) P4.33, arXiv:1912.01883,
https://arxiv.org/abs/1912.01883. Moved from `OpenConjectures/Geometry/ErdosProblem652`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem652Wanted
