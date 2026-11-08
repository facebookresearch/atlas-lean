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

/-- G is not the union of two disjoint nonempty closed sets. -/
def IsHausdorffConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ¬ ∃ (A B : Set G), IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
    Disjoint A B ∧ A ∪ B = Set.univ

/-- Any two points are joined by a continuous path. -/
def IsArcwiseConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ∀ x y : G, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = x ∧ γ 1 = y

/-- Part (2) of Scottish Book 160: every connected (in the sense of
Hausdorff) metric group is arcwise connected. -/
def ScottishBookProblem160Part2Claim : Prop :=
  ∀ (G : Type*) [MetricSpace G] [Group G] [IsTopologicalGroup G],
    IsHausdorffConnected G → IsArcwiseConnected G

/--
Part (2) of Scottish Book 160 is false. Counterexample: the p-adic
solenoid, the inverse limit of circles under `z ↦ z ^ p` (the case of
the solenoid construction with every `nᵢ = p`). It is a compact
connected metrizable topological group, but it is not path connected:
for some `x y` no continuous `γ : ℝ → G` joins them (such a `γ` would
restrict to a continuous path on `[0, 1]`). Hence connectedness in the
sense of Hausdorff does not imply arcwise connectedness for metric
groups. Part (1) is not refuted here; it remains an open conjecture
(`OpenConjectures.GroupTheory.ScottishBook160.conjecture`).
Source: Encyclopedia of Mathematics, "Solenoid" (inverse-limit
construction with `fᵢ (z) = z ^ nᵢ`, a topological group, a
one-dimensional continuum); E. Hewitt and K. A. Ross, Abstract Harmonic
Analysis I (1979), cited there; solenoids are compact metrizable
spaces that are connected but not path connected.
-/
theorem_wanted scottishBook160Part2_refuted : ¬ ScottishBookProblem160Part2Claim

end MathlibExt.GroupTheory.ScottishBook160Part2Wanted
