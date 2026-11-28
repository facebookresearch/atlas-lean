/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Filter Topology
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted

-- The sequential definition of boundedness includes the real unit interval.
example : IsBoundedSet ℝ (Set.Icc (-1) 1) := by
  intro x t hx ht
  change Tendsto (fun n => t n * x n) atTop (𝓝 (0 : ℝ))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_zero_iff_norm_tendsto_zero.mp ht)
  intro n
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (abs_le.mpr (hx n))

-- On the whole real line, reciprocal scalars can tend to zero while the products stay one.
example : ¬ IsBoundedSet ℝ Set.univ := by
  intro h
  have ht := h (fun n => (n + 1 : ℝ)) (fun n => 1 / (n + 1 : ℝ)) (fun _ => Set.mem_univ _)
    tendsto_one_div_add_atTop_nhds_zero_nat
  simp (disch := positivity) [smul_eq_mul] at ht

-- Unfold the claim to check both domains of uniform convergence and their quantifier order.
example : ¬ (∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E], IsTypeFo E →
    ∀ F : ℕ → E →ₗ[ℝ] ℝ,
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ U, |F n x| < ε) :=
  foBoundedUniformNeighborhood_refuted

-- The same unfolding for the continuous claim: its functionals are continuous linear maps.
example : ¬ (∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E], IsTypeFo E →
    ∀ F : ℕ → E →L[ℝ] ℝ,
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ U, |F n x| < ε) :=
  foBoundedUniformNeighborhood_continuous_refuted

-- Apply the continuous refutation: some space of type {F_o} carries continuous linear
-- functionals that tend to zero uniformly on every bounded set, but on no open set containing 0.
example : ∃ (E : Type) (_ : TopologicalSpace E) (_ : AddCommGroup E) (_ : Module ℝ E),
    IsTypeFo E ∧ ∃ F : ℕ → E →L[ℝ] ℝ,
      (∀ R : Set E, IsBoundedSet E R → ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ R, |F n x| < ε) ∧
      ∀ U : Set E, IsOpen U → (0 : E) ∈ U →
        ∃ ε > 0, ∀ N, ∃ n ≥ N, ∃ x ∈ U, ε ≤ |F n x| := by
  by_contra h
  refine foBoundedUniformNeighborhood_continuous_refuted fun E _ _ _ hE F hF => ?_
  by_contra hU
  refine h ⟨E, _, _, _, hE, F, hF, fun U hUo h0 => ?_⟩
  by_contra hne
  push Not at hne
  exact hU ⟨U, hUo, h0, hne⟩

-- The claim for all linear functionals implies the continuous claim, so refuting the latter is
-- the stronger result.
example : ScottishBookProblem26Claim → ScottishBookProblem26ContinuousClaim :=
  fun h E _ _ _ hE F hF => h E hE (fun n => (F n).toLinearMap) hF
