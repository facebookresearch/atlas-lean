/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.ReversibleMMQSSA

/-!
# Tests for the uniform QSSA bound for reversible Michaelis–Menten kinetics

Concrete rate constants `k₁ = kb = k₂ = kb₂ = 1` and total mass `M = 2`:

* the constants evaluate to `complexForcingConst = 6` and, on the slow window `T = 1`,
  `revSubstrateErrorConst = 15/2`; the bound `C ε` shrinks from `ε = 1/10` to `ε = 1/100`
  (computed from the definitions);
* the reduced rate is `(x - 1)/2` on `[0, 2]`, so it vanishes at the interior point `x = 1`
  (the reduced equilibrium), unlike the irreversible rate (`kb₂ = 0`), which is positive
  there; the constant `S̄ ≡ 1` solves the reduced equation (derivative computed directly);
* boundary case for `reducedRate_mono`: with `kb₂ = 3` the reduced rate decreases from
  `x = 3` to `x = 5`, both outside `[0, M]`, so the window hypothesis `x ≤ M` is not
  decorative;
* boundary case for the complex: with unprepared data `c(0) = 0` the initial distance to the
  QSS manifold is exactly `ε/2 > 0` for every `ε > 0` (the initial layer), while the substrate
  estimate holds at `τ = 0`;
* the `kb₂ = 0` bridges agree with the irreversible `qssComplex` and `mmRate` at a point;
* non-vacuity with `e_T > 0`: `exists_isSolution_nonneg` supplies a full solution with data
  `s₀ = p₀ = 1`, `c₀ = 0`, `e₀ = 1/10`, and together with `S̄ ≡ 1` it satisfies every
  hypothesis of `abs_substrate_sub_reduced_le_mul` and `abs_product_sub_reduced_le_mul`.
-/

open Real Set

namespace MathlibExtTest.Biology.Dynamics.ReversibleMMQSSA

open MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
open MathlibExt.Biology.Dynamics.MichaelisMenten (qssComplex mmRate michaelisConstant)

/-! ### Concrete constants that shrink with `ε` -/

theorem complexForcingConst_concrete : complexForcingConst 1 1 1 1 2 = 6 := by
  norm_num [complexForcingConst]

theorem revSubstrateErrorConst_concrete : revSubstrateErrorConst 1 1 1 1 2 1 = 15 / 2 := by
  norm_num [revSubstrateErrorConst, complexForcingConst]

example : revSubstrateErrorConst 1 1 1 1 2 1 * (1 / 10) = 3 / 4 := by
  rw [revSubstrateErrorConst_concrete]; norm_num

example : revSubstrateErrorConst 1 1 1 1 2 1 * (1 / 100) = 3 / 40 := by
  rw [revSubstrateErrorConst_concrete]; norm_num

/-- The constant grows with the window length: no all-time bound is claimed. -/
example : revSubstrateErrorConst 1 1 1 1 2 1 < revSubstrateErrorConst 1 1 1 1 2 2 := by
  norm_num [revSubstrateErrorConst, complexForcingConst]

/-! ### The reduced rate and its equilibrium -/

theorem reducedRate_concrete {x : ℝ} : reducedRate 1 1 1 1 2 x = (x - 1) / 2 := by
  unfold reducedRate revMMRate
  rw [div_eq_div_iff (ne_of_gt (by linarith)) (by norm_num)]
  ring

example : reducedRate 1 1 1 1 2 1 = 0 := by rw [reducedRate_concrete]; norm_num

example : reducedRate 1 1 1 1 2 0 = -1 / 2 := by rw [reducedRate_concrete]; norm_num

example : reducedRate 1 1 1 1 2 2 = 1 / 2 := by rw [reducedRate_concrete]; norm_num

/-- With an irreversible product step the rate does not vanish at `x = 1`. -/
example : reducedRate 1 1 1 0 2 1 = 1 / 3 := by norm_num [reducedRate, revMMRate]

/-- The constant `S̄ ≡ 1` solves the reduced equation `S̄' = -v(S̄, 2 - S̄)`. -/
theorem const_reduced_solution :
    ∀ τ, 0 ≤ τ → HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) (-reducedRate 1 1 1 1 2 1) τ := by
  intro τ _
  have h : -reducedRate 1 1 1 1 2 1 = 0 := by rw [reducedRate_concrete]; norm_num
  rw [h]
  exact hasDerivAt_const τ 1

/-! ### Boundary case: monotonicity needs the window `[0, M]` -/

example : reducedRate 1 1 1 3 2 5 < reducedRate 1 1 1 3 2 3 := by
  norm_num [reducedRate, revMMRate]

/-! ### Boundary case: the complex has an initial layer -/

/-- With `c(0) = 0` and `s₀ = 2`, `p₀ = 0`, the distance to the QSS manifold at `t = 0` is
`ε/2`, positive for every `ε > 0`. -/
example (ε : ℝ) : |0 - revQSSComplex 1 1 1 1 ε 2 0| = |ε| / 2 := by
  unfold revQSSComplex
  rw [zero_sub, abs_neg]
  have : (1 : ℝ) * 2 + 1 * 0 + (1 + 1) = 4 := by norm_num
  rw [this, abs_div]
  norm_num [abs_mul]
  ring

/-! ### The `kb₂ = 0` bridges at a point -/

example : revQSSComplex 1 1 1 0 1 2 5 = qssComplex 1 1 1 1 2 := by
  norm_num [revQSSComplex, qssComplex, michaelisConstant]

example : reducedRate 1 1 1 0 7 2 = mmRate 1 (michaelisConstant 1 1 1) 2 := by
  norm_num [reducedRate, revMMRate, mmRate, michaelisConstant]

/-! ### Non-vacuity with positive total enzyme -/

/-- A full solution with `e_T = 1/10 > 0` and the reduced solution `S̄ ≡ 1` satisfy the
hypotheses of both slow-window theorems. -/
example : ∃ s c e p : ℝ → ℝ, IsSolution 1 1 1 1 s c e p ∧
    ∀ τ ∈ Icc (0 : ℝ) 1,
      |s (τ / (1 / 10)) - 1| ≤ revSubstrateErrorConst 1 1 1 1 (1 + 1) 1 * (1 / 10) ∧
      |p (τ / (1 / 10)) - (1 + 1 - 1)| ≤
        (revSubstrateErrorConst 1 1 1 1 (1 + 1) 1 + 1) * (1 / 10) := by
  obtain ⟨s, c, e, p, h, hs0, hc0, he0, hp0, -⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) zero_le_one zero_le_one
      zero_le_one zero_le_one (s₀ := 1) (c₀ := 0) (e₀ := 1 / 10) (p₀ := 1) zero_le_one le_rfl
      (by norm_num) zero_le_one
  have hS : ∀ τ, 0 ≤ τ →
      HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) (-reducedRate 1 1 1 1 (1 + 1) ((fun _ ↦ 1) τ)) τ := by
    intro τ hτ
    simpa [one_add_one_eq_two] using const_reduced_solution τ hτ
  refine ⟨s, c, e, p, h, fun τ hτ ↦ ⟨?_, ?_⟩⟩
  · exact abs_substrate_sub_reduced_le_mul (one_pos) zero_le_one one_pos zero_le_one
      zero_le_one zero_le_one (by norm_num) h hs0 hc0 he0 hp0 hS rfl hτ
  · exact abs_product_sub_reduced_le_mul (one_pos) zero_le_one one_pos zero_le_one
      zero_le_one zero_le_one (by norm_num) h hs0 hc0 he0 hp0 hS rfl hτ

end MathlibExtTest.Biology.Dynamics.ReversibleMMQSSA
