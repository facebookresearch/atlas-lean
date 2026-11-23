/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.LaSalle
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Tests for LaSalle's invariance principle: the exponential-decay semiflow `ϕ t x = e^{-t} x`
on `ℝ` with Lyapunov function `V(x) = x²` (a non-vacuity witness for every hypothesis), from
which LaSalle's principle yields convergence to `0`. -/

open Filter Set Topology
open scoped NNReal omegaLimit

namespace MathlibExtTest.Dynamics.LaSalle

/-- The semiflow of `x' = -x` on `ℝ`: `ϕ t x = e^{-t} x`. -/
noncomputable def decay : Flow ℝ≥0 ℝ where
  toFun t x := Real.exp (-(t : ℝ)) * x
  cont' := by
    unfold Function.uncurry
    fun_prop
  map_add' t₁ t₂ x := by
    simp only [NNReal.coe_add, neg_add, Real.exp_add]
    ring_nf
  map_zero' x := by simp

theorem decay_apply (t : ℝ≥0) (x : ℝ) : decay t x = Real.exp (-(t : ℝ)) * x := rfl

/-- The orbit of `x` stays in the compact interval `[-|x|, |x|]`. -/
theorem decay_mem (x : ℝ) (t : ℝ≥0) : decay t x ∈ Icc (-|x|) |x| := by
  rw [decay_apply, mem_Icc, ← abs_le, abs_mul, Real.abs_exp]
  exact mul_le_of_le_one_left (abs_nonneg x) (Real.exp_le_one_iff.2 (by simp))

/-- `V(x) = x²` is nonincreasing along every orbit. -/
theorem decay_antitone (x : ℝ) : Antitone fun t => decay t x ^ 2 := by
  intro s t hst
  simp only [decay_apply, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le
    (Real.exp_le_exp.2 (neg_le_neg (NNReal.coe_le_coe.2 hst))) 2) (sq_nonneg x)

/-- Only `0` keeps `V` constant along its orbit. -/
theorem eq_zero_of_const {y : ℝ} (h : ∀ t, decay t y ^ 2 = y ^ 2) : y = 0 := by
  have h1 := h 1
  simp only [decay_apply, NNReal.coe_one, mul_pow] at h1
  have hlt : Real.exp (-1) ^ 2 < 1 := by
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    nlinarith [Real.exp_pos (-1)]
  have : (1 - Real.exp (-1) ^ 2) * y ^ 2 = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h

/-- **LaSalle in action.** Every orbit of the decay semiflow eventually enters every
neighbourhood of `0`. -/
example (x : ℝ) (U : Set ℝ) (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ∀ᶠ t in atTop, decay t x ∈ U := by
  obtain ⟨-, -, hconv⟩ := Flow.lasalle decay (continuous_pow 2) (isCompact_Icc)
    (decay_mem x) (decay_antitone x) (E := {0}) (fun y _ hy => eq_zero_of_const hy)
  refine hconv U hU ?_
  intro y hy
  have := hy 0
  simp only [decay_apply, NNReal.coe_zero, neg_zero, Real.exp_zero, one_mul,
    mem_singleton_iff] at this
  rwa [this]

/-- The ω-limit set of the decay semiflow is nonempty and consists of points whose orbit stays
at `0`. -/
example (x : ℝ) : (ω⁺ decay {x}).Nonempty :=
  (Flow.lasalle decay (continuous_pow 2) isCompact_Icc (decay_mem x) (decay_antitone x)
    (E := univ) (fun _ _ _ => trivial)).1

end MathlibExtTest.Dynamics.LaSalle
