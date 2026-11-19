/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.OneStepStability

/-! # Tests for `MathlibExt.Analysis.ODE.OneStepStability` -/

namespace MathlibExtTest.Analysis.ODE.OneStepStability

open MathlibExt.Analysis.ODE.OneStepMethod Finset Real

-- Test section: explicit Euler for `x' = -x` is stable on `[0, 1]`, since `Φ(t, x, h) = -x` is
-- `1`-Lipschitz in the state.
example : IsStable (fun (_ : ℝ) (x : ℝ) (_ : ℝ) ↦ -x) 0 1 :=
  isStable_of_lipschitzWith (L := 1) fun _ _ _ _ ↦ LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [NNReal.coe_one, one_mul, dist_neg_neg]

-- Test section: the same method with the explicit constant `e^{L (T - t₀)} = e`.
example : IsStableWith (exp 1) (fun (_ : ℝ) (x : ℝ) (_ : ℝ) ↦ -x) 0 1 := by
  have h := isStableWith_of_lipschitzWith (Φ := fun (_ : ℝ) (x : ℝ) (_ : ℝ) ↦ -x) (L := 1)
    (t₀ := 0) (T := 1) fun _ _ _ _ ↦ LipschitzWith.of_dist_le_mul fun a b ↦ by
      rw [NNReal.coe_one, one_mul, dist_neg_neg]
  simpa using h

-- Test section: explicit Euler, `Φ(t, x, h) = f(t, x)`, is stable with constant
-- `e^{L (T - t₀)}` when every `f t` is `L`-Lipschitz.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (L : NNReal)
    (hf : ∀ t, LipschitzWith L (f t)) (t₀ T : ℝ) :
    IsStableWith (exp (L * (T - t₀))) (fun t x _ ↦ f t x) t₀ T :=
  isStableWith_of_lipschitzWith fun s _ _ _ ↦ hf s

-- Test section: a zero increment is stable with any `L ≥ 0`, here `L = 0`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t₀ T : ℝ) :
    IsStable (fun (_ : ℝ) (_ : E) (_ : ℝ) ↦ (0 : E)) t₀ T :=
  isStable_of_lipschitzWith fun _ _ _ _ ↦ LipschitzWith.const (0 : E)

-- Test section: stability is not automatic. The increment `Φ(t, x, h) = x / h` doubles the state
-- at every step, whatever the step, so on the uniform grid with `J + 1` steps two runs started
-- `1` apart end `2 ^ (J + 1)` apart: no constant `S` works for every grid.
example : ¬ IsStable (fun (_ : ℝ) (x : ℝ) (h : ℝ) ↦ h⁻¹ * x) 0 1 := by
  rintro ⟨S, hS⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt S
  have hJ1 : (0 : ℝ) < J + 1 := by positivity
  have ht : ∀ j : ℕ, (j : ℝ) / (J + 1) < ((j + 1 : ℕ) : ℝ) / (J + 1) := fun j ↦ by
    push_cast
    exact div_lt_div_of_pos_right (lt_add_one _) hJ1
  have h := hS (J + 1) (fun j ↦ (j : ℝ) / (J + 1)) (by simp) (by push_cast; exact div_self hJ1.ne')
    (fun j _ ↦ ht j) (fun j ↦ 2 ^ j) (fun _ ↦ 0) (fun _ ↦ 0)
    (fun j _ ↦ by
      have hne : ((j + 1 : ℕ) : ℝ) / (J + 1) - (j : ℝ) / (J + 1) ≠ 0 := (sub_pos.2 (ht j)).ne'
      simp only [smul_eq_mul, mul_inv_cancel_left₀ hne, pow_succ]
      ring)
    (fun j _ ↦ by simp) (J + 1) (by simp)
  have hpow : ((J + 1 : ℕ) : ℝ) < 2 ^ (J + 1) := by exact_mod_cast Nat.lt_two_pow_self
  simp only [sub_zero, pow_zero, norm_zero, sum_const_zero, add_zero, norm_one, mul_one,
    norm_pow, Real.norm_ofNat] at h
  push_cast at hpow
  linarith

-- Test section: the explicit error bound on one step of explicit Euler for `x' = x` with
-- step `1/2`: from `x 0 = 1`, `z 0 = 1` and perturbation `δ 1 = 1`, the gap after one step is at
-- most `e^{1/2 - 1/2} * 1 = 1`.
example (x z : ℕ → ℝ) (hx0 : x 0 = 1) (hz0 : z 0 = 1)
    (hx : x 1 = x 0 + (1 / 2 - 0 : ℝ) • x 0) (hz : z 1 = z 0 + (1 / 2 - 0 : ℝ) • z 0 + 1) :
    ‖x 1 - z 1‖ ≤ 1 := by
  have h := norm_sub_le_of_lipschitzWith (Φ := fun (_ : ℝ) (y : ℝ) (_ : ℝ) ↦ y) (L := 1)
    (J := 1) (t := fun j ↦ (j : ℝ) / 2) (x := x) (z := z) (δ := fun _ ↦ 1)
    (fun j hj ↦ by norm_num [Nat.lt_one_iff.1 hj])
    (fun _ _ ↦ LipschitzWith.id)
    (fun j hj ↦ by obtain rfl := Nat.lt_one_iff.1 hj; show x 1 = _; rw [hx]; norm_num)
    (fun j hj ↦ by obtain rfl := Nat.lt_one_iff.1 hj; show z 1 = _; rw [hz]; norm_num)
    1 le_rfl
  norm_num [hx0, hz0] at h
  exact h

end MathlibExtTest.Analysis.ODE.OneStepStability
