/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BlackwellApproachability

open MathlibExt.GameTheory.BlackwellApproachability

/-- A non-degenerate instance: payoffs `±1` on the real line, two actions for the decision
maker against one for the opponent, and `C = {0}`. Every half-space `{x | λ x ≤ ρ}` containing
`0` has `ρ ≥ 0`, and the uniform mixed action has expected payoff `0`, so all hypotheses hold and
the Blackwell strategy brings the average payoff within `3 / √n` of `0`. -/
example : ∃ σ : ℝ → Convexity.StdSimplex ℝ (Fin 2),
    ∀ (β : ℕ → Unit) (c₀ : ℝ), c₀ ∈ ({0} : Set ℝ) → ∀ n, 0 < n →
      Metric.infDist (average (strategyPayoffs (fun a (_ : Unit) => ![(1 : ℝ), -1] a)
        (fun x => (σ x).weights) β) n) {0} ≤ (3 * 1 + ‖c₀‖) / Real.sqrt n := by
  refine blackwell_expected_approachability (R := 1) _ (Set.singleton_nonempty 0)
    isClosed_singleton (convex_singleton 0) (fun lam ρ hρ => ?_) (fun a _ => ?_)
  · refine ⟨Convexity.StdSimplex.barycenter, fun _ => ?_⟩
    have := hρ 0 rfl
    simp only [inner_zero_right] at this
    simpa [Fin.sum_univ_two, Convexity.StdSimplex.weights_barycenter_apply] using this
  · fin_cases a <;> simp

/-- The deterministic recursion on a trivial instance: constant vectors inside `C`. -/
example (C : Set ℝ) (c : ℝ) (hc : c ∈ C) (n : ℕ) :
    ((n : ℝ) * Metric.infDist (average (fun _ => c) n) C) ^ 2 ≤ n * 0 ^ 2 := by
  refine sq_mul_infDist_average_le (c := fun _ => c) (fun _ => hc) (fun m hm => ?_)
    (fun m _ => ?_) (fun _ => by simp) n
  · have havg : average (fun _ => c) m = c := by
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      simp [average, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul, hm']
    simp [havg, Metric.infDist_zero_of_mem hc]
  · simp

#print axioms sq_mul_infDist_average_le
#print axioms infDist_average_le
#print axioms blackwell_expected_approachability
