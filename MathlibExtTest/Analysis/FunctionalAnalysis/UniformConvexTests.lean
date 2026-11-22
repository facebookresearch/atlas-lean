/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.UniformConvex

import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for uniform convexity in finite dimensions and minimizing sequences
-/

open Filter Metric Set Topology

namespace UniformConvexTests

open MathlibExt.Analysis.FunctionalAnalysis.UniformConvex

/-- The distance from `2` to `[0, 1]` is `1`. -/
private lemma infDist_two_Icc : Metric.infDist (2 : ℝ) (Set.Icc 0 1) = 1 := by
  apply le_antisymm
  · calc Metric.infDist (2 : ℝ) (Set.Icc 0 1) ≤ dist 2 1 :=
        Metric.infDist_le_dist_of_mem ⟨by norm_num, by norm_num⟩
      _ = 1 := by rw [Real.dist_eq]; norm_num
  · rw [Metric.le_infDist (Set.nonempty_Icc.2 (by norm_num : (0 : ℝ) ≤ 1))]
    intro y hy
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2] : (0:ℝ) ≤ 2 - y)]
    linarith [hy.2]

/-- `ℝ` is uniformly convex, from finite-dimensional strict convexity. -/
example : UniformConvexSpace ℝ :=
  uniformConvexSpace_of_finiteDimensional_strictConvexSpace

/-- Euclidean `ℝ²` is uniformly convex, from finite-dimensional strict convexity. -/
example : UniformConvexSpace (EuclideanSpace ℝ (Fin 2)) :=
  uniformConvexSpace_of_finiteDimensional_strictConvexSpace

/-- In finite dimensions, strict and uniform convexity are equivalent:
the `ℝ` instance. -/
example : StrictConvexSpace ℝ ℝ ↔ UniformConvexSpace ℝ :=
  strictConvexSpace_iff_uniformConvexSpace_of_finiteDimensional

/-- The constant sequence at the endpoint `1` is minimizing for the distance
from `2` to `[0, 1]`, so the finite-dimensional corollary gives a unique
nearest point. -/
example : ∃! y, y ∈ Set.Icc (0 : ℝ) 1 ∧ ‖y - 2‖ = Metric.infDist 2 (Set.Icc (0 : ℝ) 1) ∧
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 y) := by
  refine exists_unique_tendsto_of_minimizingSequence_of_finiteDimensional
    (convex_Icc 0 1) isClosed_Icc (fun _ => (1 : ℝ)) (fun _ => ⟨by norm_num, by norm_num⟩) ?_
  have hfun : (fun n : ℕ => ‖(1 : ℝ) - 2‖) = fun _ => (1 : ℝ) := by
    funext n
    norm_num
  rw [hfun, infDist_two_Icc]
  exact tendsto_const_nhds

/-- Two nearest points supplied by an ordinary client are equal; neither point
needs to be a limit of the minimizing sequence. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [StrictConvexSpace ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K) {x : E} (u : ℕ → E)
    (hu : ∀ n, u n ∈ K)
    (hmin : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 (Metric.infDist x K)))
    {y z : E} (hyK : y ∈ K) (hynorm : ‖y - x‖ = Metric.infDist x K)
    (hzK : z ∈ K) (hznorm : ‖z - x‖ = Metric.infDist x K) :
    y = z := by
  obtain ⟨_, _, huniq⟩ :=
    exists_unique_nearestPoint_of_minimizingSequence_of_finiteDimensional
      hKconv hKclosed u hu hmin
  exact (huniq y ⟨hyK, hynorm⟩).trans (huniq z ⟨hzK, hznorm⟩).symm

/-- A genuinely non-constant minimizing sequence for the distance from `2`
to `[0, 1]`: `u n = 1 - (1 / 2) ^ n` lies in `[0, 1]` and its distance to
`2` tends to `1`. The minimizing-sequence theorem says it converges to a
nearest point, and that point must be `1`. -/
example : ∃ y ∈ Set.Icc (0 : ℝ) 1, ‖y - 2‖ = Metric.infDist 2 (Set.Icc (0 : ℝ) 1) ∧
    y = 1 := by
  have hu : ∀ n : ℕ, (1 - (1 / 2 : ℝ) ^ n) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    refine ⟨?_, ?_⟩
    · have h : (1 / 2 : ℝ) ^ n ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    · have h : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
      linarith
  have hmin : Tendsto (fun n : ℕ => ‖(1 - (1 / 2 : ℝ) ^ n) - 2‖) atTop
      (𝓝 (Metric.infDist 2 (Set.Icc (0 : ℝ) 1))) := by
    rw [infDist_two_Icc]
    have hfun : (fun n : ℕ => ‖(1 - (1 / 2 : ℝ) ^ n) - 2‖)
        = fun n : ℕ => 1 + (1 / 2 : ℝ) ^ n := by
      funext n
      have heq : (1 - (1 / 2 : ℝ) ^ n) - 2 = -(1 + (1 / 2 : ℝ) ^ n) := by ring
      rw [heq, norm_neg, Real.norm_of_nonneg (by positivity)]
    rw [hfun]
    have h : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h2 := h.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1))
    simpa using h2
  obtain ⟨y, hyK, hynorm, hy⟩ := exists_tendsto_of_minimizingSequence (K := Set.Icc (0 : ℝ) 1)
    (convex_Icc 0 1) isClosed_Icc (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ n) hu hmin
  refine ⟨y, hyK, hynorm, tendsto_nhds_unique hy ?_⟩
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1))
  simpa using h

end UniformConvexTests
