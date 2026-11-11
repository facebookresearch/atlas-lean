/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SIRExistence

/-! Tests for global SIR existence: the constructed solution at a concrete epidemic initial
state, the disease-free boundary `I₀ = 0` (via the exponential formula),
no transmission `β = 0`, and the boundary `S₀ = 0`. -/

open Real Set

namespace MathlibExtTest.Biology.Epidemiology.SIRExistence

open MathlibExt.Biology.Epidemiology.SIR

/-- At `(S₀, I₀, R₀) = (99/100, 1/100, 0)`, `N = 1`, `β = 2`, `γ = 1`: a global solution exists,
stays nonnegative, keeps total `1`, and the infection never dies out in finite time. -/
example : ∃ S I R : ℝ → ℝ, IsSolution 2 1 1 S I R ∧ S 0 = 99 / 100 ∧ I 0 = 1 / 100 ∧ R 0 = 0 ∧
    ∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 < I t ∧ 0 ≤ R t ∧ S t + I t + R t = 1 := by
  obtain ⟨S, I, R, h, hS, hI, hR, hnn, htot, hpos⟩ :=
    exists_isSolution_nonneg (β := 2) (N := 1) zero_le_one (S₀ := 99 / 100) (I₀ := 1 / 100)
      (R₀ := 0) (by norm_num) (by norm_num) le_rfl
  refine ⟨S, I, R, h, hS, hI, hR, fun t ht => ⟨(hnn t ht).1, (hpos t ht).2.2 (by norm_num),
    (hnn t ht).2.2, ?_⟩⟩
  rw [htot t ht]
  norm_num

/-- Disease-free initial state, via the exponential formula: `I ≡ 0` forward in time. -/
example (β γ N : ℝ) (S I R : ℝ → ℝ) (h : IsSolution β γ N S I R) (hI : I 0 = 0)
    (t : ℝ) (ht : 0 ≤ t) : I t = 0 :=
  (h.infected_eq_zero_iff ht).2 hI

/-- No transmission (`β = 0`): `S` is constant forward in time, by the exponential formula. -/
example (γ N : ℝ) (S I R : ℝ → ℝ) (h : IsSolution 0 γ N S I R) (t : ℝ) (ht : 0 ≤ t) :
    S t = S 0 := by
  rw [h.susceptible_eq_mul_exp ht]
  simp

/-- No transmission for the constructed solution at a concrete state: `S ≡ 1/2`. -/
example : ∃ S I R : ℝ → ℝ, IsSolution 0 1 1 S I R ∧ ∀ t, 0 ≤ t → S t = 1 / 2 := by
  obtain ⟨S, I, R, h, hS, -⟩ := exists_isSolution_nonneg (β := 0) (N := 1) zero_le_one
    (S₀ := 1 / 2) (I₀ := 1 / 2) (R₀ := 0) (by norm_num) (by norm_num) le_rfl
  refine ⟨S, I, R, h, fun t ht => ?_⟩
  rw [h.susceptible_eq_mul_exp ht, hS]
  simp

/-- Boundary `S₀ = 0`: no susceptibles ever, while infectives remain positive. -/
example (I₀ : ℝ) (hI₀ : 0 < I₀) : ∃ S I R : ℝ → ℝ, IsSolution 2 1 I₀ S I R ∧
    ∀ t, 0 ≤ t → S t = 0 ∧ 0 < I t := by
  obtain ⟨S, I, R, h, hS, hI, -, -, -, hpos⟩ := exists_isSolution_nonneg (β := 2) (N := I₀)
    zero_le_one (S₀ := 0) (R₀ := 0) le_rfl hI₀.le le_rfl
  exact ⟨S, I, R, h, fun t ht => ⟨(h.susceptible_eq_zero_iff ht).2 hS, (hpos t ht).2.2 hI₀⟩⟩

/-- The simplex is compact; it contains the concrete state `(99/100, 1/100, 0)` for `N = 1`. -/
example : IsCompact {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = 1} ∧
    ![99 / 100, 1 / 100, 0] ∈ {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = 1} := by
  refine ⟨isCompact_sirSimplex 1, fun i => ?_, by norm_num⟩
  fin_cases i <;> norm_num

/-- The integrating-factor lemma on `u(t) = e^{2t}`, `g = 2`. -/
example (t : ℝ) (ht : 0 ≤ t) : exp (2 * t) = exp (2 * 0) * exp (∫ _ in (0 : ℝ)..t, (2 : ℝ)) := by
  refine eq_mul_exp_integral_of_hasDerivAt (u := fun s => exp (2 * s)) (g := fun _ => 2)
    (T := t) continuousOn_const (fun s _ => ?_) t ⟨ht, le_rfl⟩
  simpa [mul_comm] using ((hasDerivAt_id s).const_mul 2).exp

end MathlibExtTest.Biology.Epidemiology.SIRExistence
