/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.ScottishBook42Wanted

/-- **Hausdorff continuity on compact convex sets.** Let $E$ be a real normed space, let
$K \subseteq E$, let $f$ be a map from subsets of $E$ to subsets of $E$, and write $d_H$ for the
Hausdorff distance between subsets of $E$. Then $f$ is Hausdorff continuous on the compact convex
subsets of $K$ if for every nonempty compact convex set $X \subseteq K$ and every
$\varepsilon > 0$ there is $\delta > 0$ such that every nonempty compact convex set
$Y \subseteq K$ with $d_H(X, Y) < \delta$ satisfies $d_H(f(X), f(Y)) < \varepsilon$.

Here $d_H$ is taken to be $0$ where the Hausdorff distance is infinite, in particular when exactly
one of the two sets is empty. The values $f(X)$ are not required to be compact, convex or
nonempty. -/
def HausdorffContinuousOnConvexCompacts {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Set E → Set E) (K : Set E) : Prop :=
  ∀ X : Set E, X ⊆ K → IsCompact X → Convex ℝ X → X.Nonempty → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Set E, Y ⊆ K → IsCompact Y → Convex ℝ Y → Y.Nonempty →
      Metric.hausdorffDist X Y < δ → Metric.hausdorffDist (f X) (f Y) < ε

/--
**Fixed point theorem for maps of compact convex sets.** Let $n \ge 0$ and let $B$ be the
closed unit ball about the origin in the Euclidean space $\mathbb{R}^n$. Let $f$ be a map from
subsets of $\mathbb{R}^n$ to subsets of $\mathbb{R}^n$ that sends every nonempty compact convex
subset of $B$ to a nonempty compact convex subset of $B$, and that is continuous in the Hausdorff
metric on the nonempty compact convex subsets of $B$. Then there is a nonempty compact convex set
$X_0 \subseteq B$ with $f(X_0) = X_0$.

This answers Ulam's Problem 42 of the Scottish Book, which asks this for closed convex sets inside
a ball $K$; inside a ball the closed convex sets are the compact ones, and the typescript's
"sphere $K$" is read as the solid ball. All sets are required to be nonempty, because the
Hausdorff distance used is degenerate at the empty set. The answer is yes: for $n \ge 2$ the space
of nonempty compact convex subsets of $B$ is homeomorphic to the Hilbert cube (Nadler, Quinn and
Stavrokas), which has the fixed-point property; for $n \le 1$ that space is a point or a $2$-cell,
and Brouwer's theorem applies.

Source: S. Ulam, Problem 42 of the Scottish Book; S. B. Nadler, J. Quinn and
N. Stavrokas, Pacific J. Math. 83 (1979), 441-462; the fixed-point theorem
for the Hilbert cube; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted fixed_point_for_convex_hyperspace_map :
    ∀ (n : ℕ) (f : Set (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n))),
      (∀ X : Set (EuclideanSpace ℝ (Fin n)),
        X ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → IsCompact X →
        Convex ℝ X → X.Nonempty →
        f X ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
        IsCompact (f X) ∧ Convex ℝ (f X) ∧ (f X).Nonempty) →
      HausdorffContinuousOnConvexCompacts f
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
      ∃ X₀ : Set (EuclideanSpace ℝ (Fin n)),
        X₀ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧ IsCompact X₀ ∧
        Convex ℝ X₀ ∧ X₀.Nonempty ∧ f X₀ = X₀

end MathlibExt.Topology.ScottishBook42Wanted
