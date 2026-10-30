/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Best approximation in finite-dimensional subspaces

A finite-dimensional subspace of a normed space is *proximinal*: every point
admits a nearest point in the subspace. The proof is a compactness argument:
minimize the distance on the sublevel set `{y : F | ‖x - y‖ ≤ infDist x F + 1}`,
which is a closed subset of a closed ball in the finite-dimensional space `F`,
hence compact, so the continuous distance function attains its minimum there;
the minimum equals `infDist x F` because the sublevel set contains points
arbitrarily close to the infimum.

In a strictly convex space the nearest point in a convex set, when it exists,
is unique: the midpoint of two distinct nearest points would be strictly
closer. Combined with existence this gives a unique best approximation in a
finite-dimensional subspace of a strictly convex space. Uniqueness can fail
without strict convexity: in `ℝ × ℝ` with the sup norm, both `(0, 0)` and
`(1, 0)` are nearest to `(1, 1)` in the `x`-axis (see the test file).

This is a companion to the projection material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` (the book's
projection proposition for closed subspaces of a Hilbert space, and its
orthogonal-decomposition proof). The book does not state proximinality for
general normed spaces. It differs from batch 42
(`ConvexProjection.lean`, nearest point in a complete convex set of an inner
product space, via the parallelogram law) by working in an arbitrary normed
space with no inner product and no completeness hypothesis on the ambient
space, and from batch 78 (`StrictConvex.lean`, uniqueness of a best
approximation in an `L^p` convex set, proved from pointwise `L^p` estimates)
by proving uniqueness from Mathlib's `StrictConvexSpace` typeclass, which
covers every strictly convex space. The complex Hilbert case is not covered
by the uniqueness statement: Mathlib's `StrictConvexSpace` API (via
`UniformConvexSpace`) is real-only.

Classical references: Rudin, *Functional Analysis*, 2nd edition, Chapter 4
(best approximation in finite-dimensional subspaces); Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, Chapter 5
(strict convexity and uniqueness of the projection).

## Main declarations

* `exists_bestApproximation_of_finiteDimensional` : every point of a normed
  space over `𝕜 = ℝ` or `ℂ` has a nearest point in a finite-dimensional
  subspace.
* `eq_of_isBestApproximation_of_strictConvexSpace` : in a strictly convex
  real normed space, two nearest points in a convex set coincide.
* `exists_unique_bestApproximation_of_finiteDimensional` : existence plus
  uniqueness for finite-dimensional subspaces of a strictly convex space.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.BestApproximation

/-- Every point of a normed space has a nearest point in a
finite-dimensional subspace (proximinality). No completeness hypothesis on
the ambient space is needed: completeness enters only through the
finite-dimensional subspace, whose closed balls are compact. -/
theorem exists_bestApproximation_of_finiteDimensional {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Submodule 𝕜 E} [FiniteDimensional 𝕜 F] (x : E) :
    ∃ y ∈ F, ∀ z ∈ F, ‖x - y‖ ≤ ‖x - z‖ := by
  set d : ℝ := Metric.infDist x (F : Set E) with hd
  have hFne : (F : Set E).Nonempty := ⟨0, F.zero_mem⟩
  have : LocallyCompactSpace 𝕜 := locallyCompact_of_proper
  have : ProperSpace ↥F := FiniteDimensional.proper 𝕜 ↥F
  set S : Set ↥F := {y | ‖x - (y : E)‖ ≤ d + 1} with hS
  have hcont : Continuous fun y : ↥F => ‖x - (y : E)‖ :=
    continuous_norm.comp (continuous_const.sub continuous_subtype_val)
  have hSclosed : IsClosed S := isClosed_le hcont continuous_const
  have hSsub : S ⊆ Metric.closedBall (0 : ↥F) (‖x‖ + d + 1) := by
    intro y hy
    have hy' : ‖x - (y : E)‖ ≤ d + 1 := hy
    have hnorm : ‖y‖ = ‖(y : E)‖ := (Submodule.norm_coe y).symm
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    calc ‖(y : E)‖ = ‖(y : E) - x + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖(y : E) - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - (y : E)‖ + ‖x‖ := by rw [norm_sub_rev]
      _ ≤ (d + 1) + ‖x‖ := by linarith [hy']
      _ = ‖x‖ + d + 1 := by ring
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ↥F) (‖x‖ + d + 1))
      hSclosed hSsub
  have hSne : S.Nonempty := by
    obtain ⟨z, hzF, hz⟩ := (Metric.infDist_lt_iff hFne).mp (by rw [← hd]; exact lt_add_one _)
    refine ⟨⟨z, hzF⟩, ?_⟩
    rw [dist_eq_norm] at hz
    exact hz.le
  obtain ⟨y₀, hy₀S, hmin⟩ := hScompact.exists_isMinOn hSne hcont.continuousOn
  have hle : ‖x - (y₀ : E)‖ ≤ d := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hδ : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨z, hzF, hz⟩ := (Metric.infDist_lt_iff hFne).mp
      (by rw [← hd]; exact lt_add_of_pos_right _ hδ)
    have hzS : (⟨z, hzF⟩ : ↥F) ∈ S := by
      rw [dist_eq_norm] at hz
      exact (lt_of_lt_of_le hz (by linarith [min_le_right ε 1])).le
    have h1 : ‖x - (y₀ : E)‖ ≤ ‖x - z‖ := hmin hzS
    rw [dist_eq_norm] at hz
    linarith [h1, hz, min_le_left ε 1]
  have hge0 : d ≤ ‖x - (y₀ : E)‖ := by
    have h2 := Metric.infDist_le_dist_of_mem (x := x) (s := (F : Set E)) y₀.2
    rw [dist_eq_norm, ← hd] at h2
    exact h2
  refine ⟨(y₀ : E), y₀.2, fun z hz => ?_⟩
  have hge : d ≤ ‖x - z‖ := by
    have h2 := Metric.infDist_le_dist_of_mem (x := x) (s := (F : Set E)) hz
    rw [dist_eq_norm, ← hd] at h2
    exact h2
  rw [le_antisymm hle hge0]
  exact hge

/-- In a strictly convex real normed space, a convex set contains at most one
point nearest to a given point: the midpoint of two distinct nearest points
would be strictly closer, by `norm_midpoint_lt_iff`. -/
theorem eq_of_isBestApproximation_of_strictConvexSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) {x y₁ y₂ : E} (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K)
    (h₁ : ∀ z ∈ K, ‖x - y₁‖ ≤ ‖x - z‖) (h₂ : ∀ z ∈ K, ‖x - y₂‖ ≤ ‖x - z‖) :
    y₁ = y₂ := by
  by_contra hne
  have hd : ‖x - y₁‖ = ‖x - y₂‖ := le_antisymm (h₁ y₂ hy₂) (h₂ y₁ hy₁)
  have huv : x - y₁ ≠ x - y₂ := fun h => hne (sub_right_injective h)
  have hmid : (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ ∈ K :=
    hK hy₁ hy₂ (by norm_num) (by norm_num) (by norm_num)
  have hlt : ‖x - ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂)‖ < ‖x - y₁‖ := by
    have hmid_eq : x - ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂)
        = (1 / 2 : ℝ) • ((x - y₁) + (x - y₂)) := by module
    rw [hmid_eq]
    exact (norm_midpoint_lt_iff hd).mpr huv
  exact (not_lt_of_ge (h₁ _ hmid)) hlt

/-- Existence plus uniqueness: a finite-dimensional subspace of a strictly
convex real normed space admits a unique best approximation to every
point. -/
theorem exists_unique_bestApproximation_of_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    {F : Submodule ℝ E} [FiniteDimensional ℝ F] (x : E) :
    ∃ y ∈ F, (∀ z ∈ F, ‖x - y‖ ≤ ‖x - z‖) ∧
      ∀ y' ∈ F, (∀ z ∈ F, ‖x - y'‖ ≤ ‖x - z‖) → y' = y := by
  obtain ⟨y, hyF, hmin⟩ :=
    exists_bestApproximation_of_finiteDimensional (𝕜 := ℝ) (F := F) x
  refine ⟨y, hyF, hmin, fun y' hy'F hmin' => ?_⟩
  exact (eq_of_isBestApproximation_of_strictConvexSpace (Submodule.convex F)
    hyF hy'F hmin hmin').symm

end MathlibExt.Analysis.Normed.Module.BestApproximation
