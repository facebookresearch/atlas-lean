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
**Separation of convex bodies at positive distance.** Let $E$ be a real Banach space and let
$A, B \subseteq E$ be convex bodies, that is, convex, closed and bounded sets with nonempty
interior. If there is $\varepsilon > 0$ with $\operatorname{dist}(a, b) \ge \varepsilon$ for all
$a \in A$ and $b \in B$, then there are a nonzero continuous linear functional
$F : E \to \mathbb{R}$ and a constant $c \in \mathbb{R}$ with $F(a) \le c$ for all $a \in A$
and $c \le F(b)$ for all $b \in B$.

Source: S. Mazur, Problem 64 of the Scottish
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
