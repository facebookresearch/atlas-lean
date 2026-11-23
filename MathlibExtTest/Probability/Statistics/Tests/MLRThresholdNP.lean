/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Tests.MLRThresholdNP

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Tests.MLRThresholdNP

/-- Fixture A (through the main theorem): the binomial threshold test at `c = 1` satisfies
the NP clauses for the pair `θ₁ = 1/4 < θ₂ = 3/4`, at the explicit threshold ratio. -/
example :
    0 ≤ ProbabilityTheory.binomialLik 2 id 1 (3 / 4 : ℝ) /
        ProbabilityTheory.binomialLik 2 id 1 (1 / 4 : ℝ) ∧
      (∀ n, (ProbabilityTheory.binomialLik 2 id 1 (3 / 4 : ℝ) /
          ProbabilityTheory.binomialLik 2 id 1 (1 / 4 : ℝ)) *
        ProbabilityTheory.binomialLik 2 id n (1 / 4 : ℝ) <
        ProbabilityTheory.binomialLik 2 id n (3 / 4 : ℝ) → 1 < n) ∧
      (∀ n, ProbabilityTheory.binomialLik 2 id n (3 / 4 : ℝ) <
        (ProbabilityTheory.binomialLik 2 id 1 (3 / 4 : ℝ) /
          ProbabilityTheory.binomialLik 2 id 1 (1 / 4 : ℝ)) *
        ProbabilityTheory.binomialLik 2 id n (1 / 4 : ℝ) → n < 1) := by
  have hMLR : ProbabilityTheory.HasMonotoneLikelihoodRatioOn
      (ProbabilityTheory.binomialLik 2 id) (Set.Icc (0 : ℝ) 1) :=
    ProbabilityTheory.binomialLik_hasMLR (monotone_id.monotoneOn _) (fun θ hθ => hθ)
  have h1 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h2 : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hlt : (1 / 4 : ℝ) < 3 / 4 := by norm_num
  have hC : Nat.choose 2 1 = 2 := rfl
  have hc : 0 < ProbabilityTheory.binomialLik 2 id 1 (1 / 4 : ℝ) := by
    unfold ProbabilityTheory.binomialLik
    show 0 < (Nat.choose 2 1 : ℝ) * (1 / 4 : ℝ) ^ 1 * (1 - 1 / 4) ^ (2 - 1)
    rw [hC]
    norm_num
  exact ProbabilityTheory.mlr_threshold_np_clauses _ _ hMLR h1 h2 hlt 1 hc

/-- Fixture B (boundary): without MLR no threshold works — for a crossing likelihood family
no `k ≥ 0` satisfies both clauses at `c = 1`. -/
example (L : ℕ → ℝ → ℝ)
    (hL : ∀ n θ, L n θ = if n = 0 then 1
      else if n = 1 then (if θ = (0 : ℝ) then 1 else 0)
      else if n = 2 then (if θ = (1 : ℝ) then 1 else 0) else 0) :
    ¬ ∃ k : ℝ, 0 ≤ k ∧
      (∀ n, k * L n 0 < L n 1 → 1 < n) ∧
      (∀ n, L n 1 < k * L n 0 → n < 1) := by
  rintro ⟨k, hk0, hrej, hacc⟩
  have h00 : L 0 0 = 1 := by simp [hL]
  have h01 : L 0 1 = 1 := by simp [hL]
  have h10 : L 1 0 = 1 := by simp [hL]
  have h11 : L 1 1 = 0 := by simp [hL]
  have e1 : k * 1 < 1 → (1 : ℕ) < 0 := by
    have h := hrej 0
    rwa [h00, h01] at h
  have hk1 : 1 ≤ k := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (e1 (by rwa [mul_one])) (by decide)
  have e2 : (0 : ℝ) < k * 1 → (1 : ℕ) < 1 := by
    have h := hacc 1
    rwa [h11, h10] at h
  have hk0' : k ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (e2 (by rwa [mul_one])) (by decide)
  linarith

/-- Fixture C (use): the Poisson family with identity mean has MLR on `(0, ∞)`. -/
example : ProbabilityTheory.HasMonotoneLikelihoodRatioOn
    (ProbabilityTheory.poissonLik id) (Set.Ioi 0) := by
  exact ProbabilityTheory.poissonLik_hasMLR (monotone_id.monotoneOn _)
    (fun θ hθ => (Set.mem_Ioi.mp hθ).le)

end MathlibExtTest.Probability.Statistics.Tests.MLRThresholdNP
