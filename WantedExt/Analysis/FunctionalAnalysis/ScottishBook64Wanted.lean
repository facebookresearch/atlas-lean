/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook64Wanted

/--
Two convex bodies in a Banach space at positive distance from each other
can be separated by a hyperplane: there is a nonzero continuous linear
functional `F` and a constant `c` with `F ≤ c` on `A` and `c ≤ F` on
`B`. A convex body here is a convex set that is closed, bounded, and
has nonempty interior. Source: S. Mazur, Problem 64 of the Scottish
Book; the theorem is true, as recorded in the typescript Ad 64
(Eidelheit, January 11, 1936), which gives the stronger statement that
separation holds even for non-disjoint bodies with no common interior
points. The positive-distance case follows from standard Hahn–Banach
separation.
-/
theorem_wanted convexBodiesSeparatedByHyperplane :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (A B : Set E),
      Convex ℝ A → IsClosed A → (interior A).Nonempty →
      (∃ R : ℝ, ∀ a ∈ A, ‖a‖ ≤ R) →
      Convex ℝ B → IsClosed B → (interior B).Nonempty →
      (∃ R : ℝ, ∀ b ∈ B, ‖b‖ ≤ R) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ A, ∀ b ∈ B, ε ≤ dist a b) →
      ∃ (F : E →L[ℝ] ℝ) (c : ℝ), F ≠ 0 ∧
        (∀ a ∈ A, F a ≤ c) ∧ (∀ b ∈ B, c ≤ F b)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook64Wanted
