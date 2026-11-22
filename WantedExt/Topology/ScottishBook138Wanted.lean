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

/-- A compact space is an absolute retract when it is a retract in every
separable metrizable space containing it: for every embedding into such a
space there is a continuous retraction back onto the embedded copy. -/
def IsAbsoluteRetract (K : Type*) [TopologicalSpace K] : Prop :=
  IsCompact (Set.univ : Set K) ∧
    ∀ (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
      [TopologicalSpace.SeparableSpace X] (e : K → X), Topology.IsEmbedding e →
      ∃ r : X → K, Continuous r ∧ Function.LeftInverse r e

/-- A set is convex in the sense of Wilson when, for every `x, y` in it and
every `t ∈ [0, 1]`, there is exactly one `z` in it with
`dist x z = t * dist x y` and `dist z y = (1 - t) * dist x y`. -/
def IsWilsonConvex (X : Type*) [PseudoMetricSpace X] (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃! z, z ∈ K ∧ dist x z = t * dist x y ∧ dist z y = (1 - t) * dist x y

/--
Both parts of Eilenberg's theorem are true. (a) Every nonempty compact convex
set in a space of type (B0) is an absolute retract. A space of type (B0) is a
Fréchet space, i.e. a complete metrizable topological vector space; the
statement is formalized in the stronger Dugundji form, for nonempty compact
convex sets in any complete metrizable locally convex topological vector
space over ℝ, which implies the (B0) case. (b) Every nonempty compact set
that is convex in the sense of Wilson is an absolute retract.
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
