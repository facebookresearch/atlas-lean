/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook160Part2Wanted

/-- **Connectedness in the sense of Hausdorff.** A topological space $G$ is connected in the
sense of Hausdorff when it is not the union of two disjoint nonempty closed subsets.

The empty space satisfies this condition. -/
def IsHausdorffConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ¬ ∃ (A B : Set G), IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
    Disjoint A B ∧ A ∪ B = Set.univ

/-- **Arcwise connected space.** A topological space $G$ is arcwise connected when for any two
points $x, y \in G$ there is a continuous map $\gamma \colon \mathbb{R} \to G$ with
$\gamma(0) = x$ and $\gamma(1) = y$.

Restricting $\gamma$ to $[0, 1]$ gives a path from $x$ to $y$, and every such path extends
to $\mathbb{R}$, so this says that any two points are joined by a path; the path need not be
injective. -/
def IsArcwiseConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ∀ x y : G, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = x ∧ γ 1 = y

/-- **Claim of Scottish Book Problem 160, part (2).** The claim that every metric group $G$
(a group with a metric for which multiplication and inversion are continuous) that is
connected in the sense of Hausdorff is arcwise connected. -/
def ScottishBookProblem160Part2Claim : Prop :=
  ∀ (G : Type*) [MetricSpace G] [Group G] [IsTopologicalGroup G],
    IsHausdorffConnected G → IsArcwiseConnected G

/--
**Connected metric groups need not be arcwise connected.** The claim of part (2) of Scottish
Book Problem 160 is false: there is a metric group $G$ (a group with a metric for which
multiplication and inversion are continuous) that is connected in the sense of Hausdorff but
not arcwise connected, that is, there are points $x, y \in G$ such that no continuous map
$\gamma \colon \mathbb{R} \to G$ has $\gamma(0) = x$ and $\gamma(1) = y$.

The $p$-adic solenoid, the inverse limit of circles under $z \mapsto z^p$, is such a group:
it is a compact connected metrizable topological group that is not path connected.

Source: Encyclopedia of Mathematics, "Solenoid" (inverse-limit
construction with `fᵢ (z) = z ^ nᵢ`, a topological group, a
one-dimensional continuum); E. Hewitt and K. A. Ross, Abstract Harmonic
Analysis I (1979), cited there; solenoids are compact metrizable
spaces that are connected but not path connected.
-/
theorem_wanted scottishBook160Part2_refuted : ¬ ScottishBookProblem160Part2Claim

end MathlibExt.GroupTheory.ScottishBook160Part2Wanted
