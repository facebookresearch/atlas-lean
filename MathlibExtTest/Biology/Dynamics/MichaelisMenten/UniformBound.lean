/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.MichaelisMenten.UniformBound

/-!
# Tests for the uniform QSSA bound for Michaelis–Menten kinetics

Concrete rate constants `k₁ = kb = k₂ = 1` (so `K_M = 2`), initial substrate `s₀ = 2` and slow
window `T = 1`:

* the explicit constants evaluate to `substrateErrorConst = 15/4`,
  `rateErrorBound(τ₀ = 1) = e^{-2/ε} + 21 ε / 8`, and `preparedRateBound = ε (3 + ε)(5 + ε)/8`,
  and each shrinks from `ε = 1/10` to `ε = 1/100` (computed from the definitions);
* boundary case: with unprepared data `c(0) = 0`, the slow-time rate-law error at `τ = 0` is
  exactly `1/2` for every `ε > 0`, so no bound tending to zero holds inside the initial layer;
  the bound with `τ₀ = 0` stays `≥ 1`; with prepared data `c(0) = q(s₀)` the error at `τ = 0`
  is `0` (all computed from the definitions, not from the theorems);
* non-vacuity: the enzyme-free solution satisfies every hypothesis of the real-time theorems,
  and a reduced solution exists (`exists_reduced_solution`).
-/

open Filter Topology Real Set

namespace MathlibExtTest.Biology.Dynamics.MichaelisMenten.UniformBound

open MathlibExt.Biology.Dynamics.MichaelisMenten

/-! ### Smoke test: the API used by the bound -/

example : michaelisConstant 1 1 1 = 2 := by norm_num [michaelisConstant]

example : qssComplex 1 1 1 1 2 = 1 / 2 := by norm_num [qssComplex, michaelisConstant]

example : mmRate 1 2 2 = 1 / 2 := by norm_num [mmRate]

/-! ### Concrete constants that shrink with `ε` -/

/-- The substrate constant at `k₁ = kb = k₂ = 1`, `s₀ = 2`, `T = 1`. -/
theorem substrateErrorConst_concrete : substrateErrorConst 1 1 1 2 1 = 15 / 4 := by
  norm_num [substrateErrorConst, michaelisConstant]

/-- The substrate error bound `C ε` at `ε = 1/10` and `ε = 1/100`. -/
example : substrateErrorConst 1 1 1 2 1 * (1 / 10) = 3 / 8 := by
  rw [substrateErrorConst_concrete]; norm_num

example : substrateErrorConst 1 1 1 2 1 * (1 / 100) = 3 / 80 := by
  rw [substrateErrorConst_concrete]; norm_num

/-- The rate-law bound outside the initial layer (`τ₀ = 1`) in closed form. -/
theorem rateErrorBound_concrete (ε : ℝ) :
    rateErrorBound 1 1 1 2 1 1 ε = exp (-2 / ε) + 21 / 8 * ε := by
  rw [rateErrorBound, substrateErrorConst_concrete]
  norm_num [michaelisConstant]
  ring_nf

/-- The rate-law bound shrinks from `ε = 1/10` to `ε = 1/100`. -/
example : rateErrorBound 1 1 1 2 1 1 (1 / 100) < rateErrorBound 1 1 1 2 1 1 (1 / 10) := by
  rw [rateErrorBound_concrete, rateErrorBound_concrete]
  have : exp (-2 / (1 / 100)) < exp (-2 / (1 / 10)) := exp_lt_exp.2 (by norm_num)
  linarith

/-- The prepared-data bound in closed form. -/
theorem preparedRateBound_concrete (ε : ℝ) :
    preparedRateBound 1 1 1 2 1 ε = ε * (3 + ε) * (5 + ε) / 8 := by
  norm_num [preparedRateBound, michaelisConstant]
  ring

example : preparedRateBound 1 1 1 2 1 (1 / 100) < preparedRateBound 1 1 1 2 1 (1 / 10) := by
  rw [preparedRateBound_concrete, preparedRateBound_concrete]; norm_num

/-- The limits, through the general theorems. -/
example : Tendsto (rateErrorBound 1 1 1 2 1 1) (𝓝[>] 0) (𝓝 0) :=
  tendsto_rateErrorBound (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (preparedRateBound 1 1 1 2 1) (𝓝[>] 0) (𝓝 0) := tendsto_preparedRateBound

/-! ### Boundary case: the initial layer -/

/-- **Inside the initial layer the rate law fails.** For every `ε > 0`, every solution with
unprepared data `c(0) = 0` and every reduced solution with `S̄(0) = 2`, the slow-time rate-law
error at `τ = 0` is exactly `1/2`, independently of `ε`. Computed from the definitions. -/
theorem rate_error_at_zero_unprepared {ε : ℝ} {c S : ℝ → ℝ} (hc : c 0 = 0) (hS : S 0 = 2) :
    |1 * c (0 / ε) / ε - mmRate 1 (michaelisConstant 1 1 1) (S 0)| = 1 / 2 := by
  rw [zero_div, hc, hS]
  norm_num [mmRate, michaelisConstant]

/-- Hence no bound of order `ε` can hold at `τ = 0` without prepared data: for every `C`
there is `ε > 0` beating it, for every such solution. -/
theorem not_bigO_at_zero_unprepared (C : ℝ) :
    ∃ ε > 0, ∀ c S : ℝ → ℝ, c 0 = 0 → S 0 = 2 →
      C * ε < |1 * c (0 / ε) / ε - mmRate 1 (michaelisConstant 1 1 1) (S 0)| := by
  refine ⟨1 / (2 * (|C| + 1)), by positivity, fun c S hc hS ↦ ?_⟩
  rw [rate_error_at_zero_unprepared hc hS]
  have h1 : C * (1 / (2 * (|C| + 1))) ≤ |C| * (1 / (2 * (|C| + 1))) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h2 : |C| * (1 / (2 * (|C| + 1))) < 1 / 2 := by
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith [abs_nonneg C]
  linarith

/-- The rate-law bound with `τ₀ = 0` does not shrink: it is at least `k₂ = 1` for every
`ε`. Computed from the definition. -/
example {ε : ℝ} (hε : 0 < ε) : 1 ≤ rateErrorBound 1 1 1 2 1 0 ε := by
  rw [rateErrorBound, substrateErrorConst_concrete]
  norm_num [michaelisConstant]
  positivity

/-- The general rate theorem's initial-layer term at `τ = 0` is `|0 - q(s₀)|/ε = 1/2`,
matching the actual error above: the layer term is attained. -/
example {ε : ℝ} (hε : 0 < ε) :
    |0 - qssComplex 1 1 1 ε 2| / ε * exp (-(1 + 1) * 0 / ε) = 1 / 2 := by
  norm_num [qssComplex, michaelisConstant]
  rw [abs_of_pos (by positivity)]
  field_simp
  norm_num

/-- **Prepared data removes the layer**: with `c(0) = q(s₀)` the rate-law error at `τ = 0` is
`0`. Computed from the definitions. -/
example {ε : ℝ} (hε : 0 < ε) {c S : ℝ → ℝ} (hc : c 0 = qssComplex 1 1 1 ε 2) (hS : S 0 = 2) :
    |1 * c (0 / ε) / ε - mmRate 1 (michaelisConstant 1 1 1) (S 0)| = 0 := by
  rw [zero_div, hc, hS]
  norm_num [qssComplex, mmRate, michaelisConstant]
  field_simp
  norm_num

/-! ### Non-vacuity -/

/-- The enzyme-free solution `(s, c, e, p) = (2, 0, 0, 0)` solves the mass-action system;
it satisfies `s(0) > 0`, `c(0) ≥ 0`, `e(0) ≥ 0`. Computed from the definitions. -/
theorem isSolution_enzymeFree :
    IsSolution 1 1 1 (fun _ ↦ 2) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) := by
  refine ⟨fun t _ ↦ ?_, fun t _ ↦ ?_, fun t _ ↦ ?_, fun t _ ↦ ?_⟩
  · simpa [substrateRate] using hasDerivAt_const t (2 : ℝ)
  · simpa [complexRate] using hasDerivAt_const t (0 : ℝ)
  · simpa [complexRate] using hasDerivAt_const t (0 : ℝ)
  · simpa using hasDerivAt_const t (0 : ℝ)

/-- The hypotheses of the real-time slaving and substrate theorems are jointly satisfiable:
the enzyme-free solution and a reduced solution through `s₀ = 2`. -/
example : ∃ S : ℝ → ℝ,
    |(fun _ ↦ (2 : ℝ)) 1 - S ((0 + 0) * 1)| ≤ |(2 : ℝ) - S 0| + (1 * (2 + 0) + 1) *
      (|0 - qssComplex 1 1 1 (0 + 0) 2| / (1 + 1) +
        (0 + 0) ^ 2 * (1 * (2 + 0) + 1) / michaelisConstant 1 1 1 / (1 + 1) * 1) := by
  obtain ⟨S, hS, hS0, hSpos⟩ :=
    exists_reduced_solution (k₂ := 1) (K := michaelisConstant 1 1 1) (s₀ := 2)
      (by norm_num [michaelisConstant]) (by norm_num)
  exact ⟨S, isSolution_enzymeFree.abs_substrate_sub_reduced_le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl le_rfl (fun τ _ ↦ hS τ) (hSpos 0) zero_le_one⟩

/-- The first-order Tikhonov estimate in the `WantedExt` form, instantiated at the concrete
rate constants with an actual reduced solution. -/
example : ∃ S : ℝ → ℝ, S 0 = 2 ∧ ∃ C : ℝ, ∀ e₀ : ℝ, 0 < e₀ → ∀ s c e p : ℝ → ℝ,
    IsSolution 1 1 1 s c e p → s 0 = 2 → c 0 = 0 → e 0 = e₀ →
      ∀ τ ∈ Icc 0 1, |s (τ / e₀) - S τ| ≤ C * e₀ := by
  obtain ⟨S, hS, hS0, -⟩ :=
    exists_reduced_solution (k₂ := 1) (K := michaelisConstant 1 1 1) (s₀ := 2)
      (by norm_num [michaelisConstant]) (by norm_num)
  exact ⟨S, hS0, exists_abs_substrate_sub_reduced_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun τ _ ↦ hS τ) hS0⟩

end MathlibExtTest.Biology.Dynamics.MichaelisMenten.UniformBound
