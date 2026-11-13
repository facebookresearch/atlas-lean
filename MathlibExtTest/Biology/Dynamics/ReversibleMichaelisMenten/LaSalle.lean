/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten.LaSalle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Tests for convergence of reversible Michaelis–Menten kinetics.

* Reversible Michaelis–Menten with all rate constants `1` and initial state
  `(s, c, e, p) = (1, 0, 1, 0)` on the boundary of the orthant: the solution is positive for
  `t > 0` and converges to the equilibrium
  `((√3 - 1)/2, 2 - √3, √3 - 1, (√3 - 1)/2)`, computed by hand. -/

open Set Filter Metric
open scoped Topology

namespace MathlibExtTest.Biology.Dynamics.ReversibleMichaelisMenten.LaSalle

open MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmCurve)

/-- The equilibrium of the class `e + c = 1`, `s + c + p = 1` for rate constants `1, 1, 1, 1`,
computed by hand: detailed balance `e s = c = e p` gives `s = p = (1 - c)/2` and
`c² - 4c + 1 = 0`, so `c = 2 - √3`. -/
noncomputable def mmEq : Fin 4 → ℝ :=
  ![(√3 - 1) / 2, 2 - √3, √3 - 1, (√3 - 1) / 2]

theorem mmEq_spec : (∀ i, 0 ≤ mmEq i) ∧ mmEq 2 + mmEq 1 = 1 ∧ mmEq 0 + mmEq 1 + mmEq 3 = 1 ∧
    revField 1 1 1 1 mmEq = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1 : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨fun i => ?_, ?_, ?_, revField_eq_zero_iff.2 ⟨?_, ?_⟩⟩
  · fin_cases i <;> simp [mmEq] <;> linarith
  all_goals simp only [mmEq, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  · ring
  · ring
  · nlinarith
  · nlinarith

/-- The orbital derivative of the pseudo-Helmholtz function relative to `mmEq` vanishes at
`mmEq` and is `< 0` at the positive non-equilibrium state `(2, 1, 1, 1)`. -/
example : mmNetwork.helmholtzRate (mmRates 1 1 1 1) mmEq mmEq = 0 ∧
    mmNetwork.helmholtzRate (mmRates 1 1 1 1) mmEq ![2, 1, 1, 1] < 0 := by
  obtain ⟨h0, hE, hS, hf⟩ := mmEq_spec
  have hpos := pos_of_equilibrium (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) one_pos one_pos
    one_pos one_pos one_pos one_pos h0 hE hS hf
  have H := fun x hx => helmholtzRate_mmNetwork_nonpos (k₁ := 1) (kb := 1) (k₂ := 1)
    (kb₂ := 1) one_pos one_pos one_pos one_pos (x := x) hpos hf hx
  have h2 : ∀ i, 0 < (![2, 1, 1, 1] : Fin 4 → ℝ) i := fun i => by fin_cases i <;> norm_num
  refine ⟨(H mmEq hpos).2.2 hf, lt_of_le_of_ne (H _ h2).1 fun h => ?_⟩
  have := congrFun ((H _ h2).2.1 h) 0
  norm_num [revField, MathlibExt.Biology.Dynamics.MichaelisMenten.substrateRate] at this

/-- **Non-vacuity and the hand-computed limit.** With all rate constants `1`, the solution from
the boundary state `(1, 0, 1, 0)` (no complex, no product) is strictly positive at `t = 1` and
converges to `mmEq = ((√3 - 1)/2, 2 - √3, √3 - 1, (√3 - 1)/2)`. -/
theorem mm_boundary_start :
    ∃ s c e p : ℝ → ℝ, IsSolution 1 1 1 1 s c e p ∧ s 0 = 1 ∧ c 0 = 0 ∧ e 0 = 1 ∧ p 0 = 0 ∧
      (0 < s 1 ∧ 0 < c 1 ∧ 0 < e 1 ∧ 0 < p 1) ∧ Tendsto (mmCurve s c e p) atTop (𝓝 mmEq) := by
  obtain ⟨s, c, e, p, h, hs, hc, he, hp, -, -, -⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) zero_le_one zero_le_one
      zero_le_one zero_le_one zero_le_one le_rfl zero_le_one le_rfl
  have hpos := h.pos one_pos one_pos one_pos one_pos (by rw [hs]; exact zero_le_one)
    (by rw [hc]) (by rw [he]; exact zero_le_one) (by rw [hp]) (by rw [he, hc]; norm_num)
    (by rw [hs, hc, hp]; norm_num) one_pos
  obtain ⟨xs, hxs, hxsE, hxsS, hxsf, hlim⟩ := h.tendsto_equilibrium one_pos one_pos one_pos
    one_pos (by rw [hs]; exact zero_le_one) (by rw [hc]) (by rw [he]; exact zero_le_one)
    (by rw [hp]) (by rw [he, hc]; norm_num) (by rw [hs, hc, hp]; norm_num)
  have hxs_eq : xs = mmEq := (existsUnique_equilibrium (k₁ := 1) (kb := 1) (k₂ := 1)
      (kb₂ := 1) one_pos one_pos one_pos one_pos (eT := 1) (sT := 1) one_pos one_pos).unique
    ⟨fun i => (hxs i).le, by rw [hxsE, he, hc]; norm_num, by rw [hxsS, hs, hc, hp]; norm_num,
      hxsf⟩ mmEq_spec
  exact ⟨s, c, e, p, h, hs, hc, he, hp, hpos, hxs_eq ▸ hlim⟩

end MathlibExtTest.Biology.Dynamics.ReversibleMichaelisMenten.LaSalle
