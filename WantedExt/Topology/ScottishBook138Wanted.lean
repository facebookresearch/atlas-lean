/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.ScottishBook138Wanted

/-- **Absolute retract.** A topological space $K$ is an absolute retract when $K$ is compact
and, for every separable metrizable space $X$ and every topological embedding
$e \colon K \to X$, there is a continuous map $r \colon X \to K$ with $r(e(k)) = k$ for all
$k \in K$. -/
def IsAbsoluteRetract (K : Type*) [TopologicalSpace K] : Prop :=
  IsCompact (Set.univ : Set K) ∧
    ∀ (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
      [TopologicalSpace.SeparableSpace X] (e : K → X), Topology.IsEmbedding e →
      ∃ r : X → K, Continuous r ∧ Function.LeftInverse r e

/-- **Wilson convexity.** A subset $K$ of a pseudometric space $X$ with distance $d$ is convex in
the sense of Wilson when for all $x, y \in K$ and every real $t$ with $0 \le t \le 1$ there is
exactly one $z \in K$ with $d(x, z) = t \, d(x, y)$ and $d(z, y) = (1 - t) \, d(x, y)$. -/
def IsWilsonConvex (X : Type*) [PseudoMetricSpace X] (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃! z, z ∈ K ∧ dist x z = t * dist x y ∧ dist z y = (1 - t) * dist x y

/--
**Eilenberg's theorem on compact convex absolute retracts.** (a) Every nonempty compact
convex subset of a complete metrizable locally convex topological vector space over
$\mathbb{R}$ is an absolute retract. (b) Every nonempty compact subset of a pseudometric
space that is convex in the sense of Wilson is an absolute retract.

The spaces in part (a) are the real Fréchet spaces, the spaces of type (B0).

Source: S. Eilenberg, Problem 138 of the Scottish Book; the typescript heads
the entry "Theorem; Eilenberg" and states both (a) and (b) as theorems. Part
(a) is also the Dugundji theorem, see the 2026 survey "90+ years of the
Scottish Book" (arXiv:2603.27867), which notes that every nonempty convex
subset of a locally convex metrizable topological vector space is an absolute
retract.
-/
theorem_wanted eilenbergCompactConvexAbsoluteRetract :
    (∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E]
      [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [CompleteSpace E]
      [TopologicalSpace.MetrizableSpace E]
      (K : Set E), Convex ℝ K → K.Nonempty → IsCompact K → IsAbsoluteRetract ↥K) ∧
    ∀ (X : Type*) [PseudoMetricSpace X] (K : Set X),
      IsCompact K → K.Nonempty → IsWilsonConvex X K → IsAbsoluteRetract ↥K

end MathlibExt.Topology.ScottishBook138Wanted
