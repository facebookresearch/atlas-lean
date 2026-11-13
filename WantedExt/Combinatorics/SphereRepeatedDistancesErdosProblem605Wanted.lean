/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Repeated distances on the sphere (Erdős Problem 605)

Erdős Problem 605: is there some function `f(n) → ∞` such that there exist `n` distinct points on
the surface of a two-dimensional sphere with at least `f(n) n` many pairs of points whose distances
are the same?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #605, https://www.erdosproblems.com/605 (status
PROVED). UnsolvedMath record UM-30006947 (`EP-605`), dataset ulamai/UnsolvedMath v1.8.0.

The sphere is the unit sphere in `ℝ³` (`EuclideanSpace ℝ (Fin 3)`); by scaling this loses nothing.
Pairs are unordered pairs of distinct points; the common distance `δ` may depend on the point set.
-/

open Classical in
/-- **Number of pairs at a given distance.** For a finite set $P$ of points in $\mathbb{R}^3$ and a
real number $\delta$, this is the number of unordered pairs $\{p, q\}$ of distinct points
$p, q \in P$ with Euclidean distance $|p - q| = \delta$, computed as half the number of ordered
pairs $(p, q)$ of distinct points of $P$ at distance $\delta$ and taken as a real number. -/
noncomputable def pairsAtDistance (P : Finset (EuclideanSpace ℝ (Fin 3))) (δ : ℝ) : ℝ :=
  ((P.offDiag.filter fun pq => dist pq.1 pq.2 = δ).card : ℝ) / 2

/-- **Erdős Problem 605 (repeated distances on the sphere).** The proposition that there is a
function $f : \mathbb{N} \to \mathbb{R}$ with $f(n) \to \infty$ as $n \to \infty$ such that for
every $n \in \mathbb{N}$ there are a set $P$ of $n$ distinct points on the unit sphere
$\{x \in \mathbb{R}^3 : \|x\| = 1\}$ and a real number $\delta$ for which the number of unordered
pairs of distinct points of $P$ at distance $\delta$ is at least $f(n) \cdot n$. -/
def sphereRepeatedDistanceSuperlinear : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧ ∀ n : ℕ,
    ∃ P : Finset (EuclideanSpace ℝ (Fin 3)), P.card = n ∧ (∀ p ∈ P, ‖p‖ = 1) ∧
      ∃ δ : ℝ, f n * n ≤ pairsAtDistance P δ

/--
**Erdős Problem 605 is true.** There is a function $f : \mathbb{N} \to \mathbb{R}$ with
$f(n) \to \infty$ as $n \to \infty$ such that for every $n \in \mathbb{N}$ there are a set $P$ of
$n$ distinct points on the unit sphere $\{x \in \mathbb{R}^3 : \|x\| = 1\}$ and a real number
$\delta$ for which the number of unordered pairs of distinct points of $P$ at distance $\delta$
is at least $f(n) \cdot n$.

Erdős, Hickerson and Pach (Theorem 2(ii)) found an absolute constant $c > 0$ such that for every
$n$ there are $n$ points on the unit sphere each at distance $\sqrt{2}$ from at least
$c n^{1/3}$ others, hence at least $c n^{4/3} / 2$ pairs at distance $\sqrt{2}$;
erdosproblems.com/605 lists the problem as proved.

Source: T. F. Bloom,
Erdős Problems, Problem #605, https://www.erdosproblems.com/605 (status PROVED); resolution: P.
Erdős, D. Hickerson and J. Pach, A problem of Leo Moser about repeated distances on the sphere,
Amer. Math. Monthly (1989), 569-575, Theorem 2(ii): for every n there are n points on the unit
sphere S² each at distance √2 from at least c₂ n^{1/3} others; Theorem 2(i): for every 0 < α < 2, n
points each at distance α from at least c₁ log* n others, https://www.erdosproblems.com/605.
-/
public theorem_wanted sphereRepeatedDistanceSuperlinear_holds : sphereRepeatedDistanceSuperlinear

end MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605Wanted
