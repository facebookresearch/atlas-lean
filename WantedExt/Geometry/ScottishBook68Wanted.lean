/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook68Wanted

/--
**Ulam's flat-sections problem in dimension three.** Let $K \subseteq \mathbb{R}^3$ be a compact
set homeomorphic to the closed unit ball. Suppose that for every nonzero continuous linear
functional $F : \mathbb{R}^3 \to \mathbb{R}$ and every real $c$ such that the plane
$\{x : F(x) = c\}$ meets the interior of $K$, the intersection of this plane with the boundary
(frontier) of $K$ is homeomorphic to the unit circle. Then $K$ is convex.

Only planes meeting the interior of $K$ are constrained: a supporting plane can meet the
boundary in a single point, as the plane $\{x : x_1 = 1\}$ does for the closed unit ball, so
requiring a circle for every plane would make the hypothesis impossible. Allowing empty or
one-point sections for the other planes would still exclude convex bodies such as the cube,
whose face planes meet its boundary in a square.

Source: S. Ulam, Problem 68 of the Scottish Book, asking to prove that
a manifold whose every hyperplane section of its boundary is a sphere
is convex. Montejano gave a complete solution, settling the problem
affirmatively: L. Montejano, "About a problem of Ulam concerning flat
sections of manifolds", Comment. Math. Helv. 65 (1990), 462–473; see
also Montejano, "Three old problems from the Polish school of
mathematics", Bol. Soc. Mat. Mex. (3) 30 (2024).
-/
theorem_wanted ulamFlatSectionsConvex :
    ∀ (K : Set (EuclideanSpace ℝ (Fin 3))),
      IsCompact K →
      Nonempty (K ≃ₜ Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (∀ (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (c : ℝ), F ≠ 0 →
        (∃ x ∈ interior K, F x = c) →
        Nonempty (↥(frontier K ∩ {x | F x = c}) ≃ₜ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) →
      Convex ℝ K

end MathlibExt.Geometry.ScottishBook68Wanted
