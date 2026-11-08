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

/-- `f` depends continuously, in the Hausdorff metric, on compact convex
subsets of `K`: an epsilon-delta statement using `Metric.hausdorffDist`. -/
def HausdorffContinuousOnConvexCompacts {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Set E → Set E) (K : Set E) : Prop :=
  ∀ X : Set E, X ⊆ K → IsCompact X → Convex ℝ X → X.Nonempty → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Set E, Y ⊆ K → IsCompact Y → Convex ℝ Y → Y.Nonempty →
      Metric.hausdorffDist X Y < δ → Metric.hausdorffDist (f X) (f Y) < ε

/--
Ulam, Problem 42 of the Scottish Book. Original question: suppose that to
every convex closed set `X` inside a ball `K` in Euclidean space there is
assigned another convex closed set `f(X)` inside `K`, depending continuously
on `X` in the Hausdorff metric; must there be a fixed point, a closed convex
`X₀` with `f(X₀) = X₀`? All sets in the statement are required nonempty:
nonemptiness restores the ordinary Hausdorff-metric meaning, since Mathlib's
`Metric.hausdorffDist` is degenerate at `∅` (`hausdorffDist s ∅ = 0` for all
`s`, so without it a map sending every nonempty set to `∅` and `∅` to a point
would vacuously satisfy the continuity and codomain conditions while having no
fixed point). The answer is yes: the hyperspace of compact convex
subsets of `K` is homeomorphic to the Hilbert cube `Q` (Nadler-Quinn-
Stavrokas), and every continuous map from `Q` to itself has a fixed point, the
infinite-dimensional extension of Brouwer's theorem. The typescript says
"sphere `K`"; it is read as the solid ball, since convex sets are contained
in it.
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
