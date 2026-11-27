/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Functions with zero fourth derivative on an interval

## i. Overview

On `[0, L]`, a differentiable function whose derivative vanishes on the open interval `(0, L)`
takes the same value at any two points, and a `C⁴` function whose fourth derivative vanishes on
`(0, L)` agrees with a cubic polynomial on `[0, L]`. Both follow from the mean value theorem
`exists_deriv_eq_slope`, applied to the third, second and first derivatives and to the function
minus the accumulated polynomial. For `L < 0` both intervals are empty and the statements are
trivial.

## ii. Key results

- `MathlibExt.Analysis.Calculus.ZeroFourthDerivative.eq_of_deriv_eq_zero_on_Ioo`: constancy on
  `[0, L]`.
- `MathlibExt.Analysis.Calculus.ZeroFourthDerivative.exists_cubic_of_iteratedDeriv_four_eq_zero`:
  zero fourth derivative gives a cubic on `[0, L]`.

## iii. Table of contents

- A. Constancy and the cubic

## iv. References

- W. Rudin, *Principles of Mathematical Analysis*, 3rd edition, 1976 (mean value theorem).
-/

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ZeroFourthDerivative

/-! ## A. Constancy and the cubic -/

/-- A differentiable function whose derivative vanishes on `(0, L)` takes the same value at any
two points of `[0, L]` (mean value theorem). -/
lemma eq_of_deriv_eq_zero_on_Ioo {L : ℝ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ x ∈ Set.Ioo (0 : ℝ) L, deriv f x = 0) {a x : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) L)
    (hx : x ∈ Set.Icc (0 : ℝ) L) : f x = f a := by
  rcases lt_trichotomy a x with hax | rfl | hxa
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hax hf.continuous.continuousOn
      hf.differentiableOn
    rw [h c ⟨by linarith [ha.1, hc.1], by linarith [hx.2, hc.2]⟩] at hcd
    have hne : x - a ≠ 0 := by linarith
    field_simp at hcd
    linarith
  · rfl
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hxa hf.continuous.continuousOn
      hf.differentiableOn
    rw [h c ⟨by linarith [hx.1, hc.1], by linarith [ha.2, hc.2]⟩] at hcd
    have hne : a - x ≠ 0 := by linarith
    field_simp at hcd
    linarith

/-- Homogeneous step: a `C⁴` function with zero fourth derivative on `(0, L)` is a cubic on
`[0, L]`. -/
lemma exists_cubic_of_iteratedDeriv_four_eq_zero {L : ℝ} {d : ℝ → ℝ} (hd : ContDiff ℝ 4 d)
    (h4 : ∀ x ∈ Set.Ioo (0 : ℝ) L, iteratedDeriv 4 d x = 0) :
    ∃ c₀ c₁ c₂ c₃ : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) L, d x = c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 := by
  rcases lt_or_ge L 0 with hL | hL
  · exact ⟨0, 0, 0, 0, fun x hx => absurd (hx.1.trans hx.2) (not_le.mpr hL)⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hL⟩
  have hD : ∀ k : ℕ, k < 4 → Differentiable ℝ (iteratedDeriv k d) := fun k hk =>
    hd.differentiable_iteratedDeriv k (by exact_mod_cast hk)
  have hs : ∀ k : ℕ, deriv (iteratedDeriv k d) = iteratedDeriv (k + 1) d := fun k =>
    (iteratedDeriv_succ).symm
  set k3 := iteratedDeriv 3 d 0
  set k2 := iteratedDeriv 2 d 0
  set k1 := iteratedDeriv 1 d 0
  have e3 : ∀ x ∈ Set.Icc (0 : ℝ) L, iteratedDeriv 3 d x = k3 := fun x hx =>
    eq_of_deriv_eq_zero_on_Ioo (hD 3 (by norm_num)) (fun y hy => by rw [hs 3]; exact h4 y hy) h0 hx
  have e2 : ∀ x ∈ Set.Icc (0 : ℝ) L, iteratedDeriv 2 d x = k2 + k3 * x := by
    intro x hx
    have hg : Differentiable ℝ (fun y : ℝ => k3 * y) := by fun_prop
    have := eq_of_deriv_eq_zero_on_Ioo (f := fun y => iteratedDeriv 2 d y - k3 * y)
      ((hD 2 (by norm_num)).sub hg) (fun y hy => by
        have hgd : HasDerivAt (fun y : ℝ => k3 * y) k3 y := by
          simpa using (hasDerivAt_id' y).const_mul k3
        rw [deriv_fun_sub ((hD 2 (by norm_num)) y) (hg y), hgd.deriv, congrFun (hs 2) y,
          e3 y (Set.Ioo_subset_Icc_self hy)]
        ring) h0 hx
    simp only [mul_zero, sub_zero] at this
    linarith
  have e1 : ∀ x ∈ Set.Icc (0 : ℝ) L, iteratedDeriv 1 d x = k1 + k2 * x + k3 / 2 * x ^ 2 := by
    intro x hx
    have hg : Differentiable ℝ (fun y : ℝ => k2 * y + k3 / 2 * y ^ 2) := by fun_prop
    have := eq_of_deriv_eq_zero_on_Ioo
      (f := fun y => iteratedDeriv 1 d y - (k2 * y + k3 / 2 * y ^ 2))
      ((hD 1 (by norm_num)).sub hg) (fun y hy => by
        have hgd : HasDerivAt (fun y : ℝ => k2 * y + k3 / 2 * y ^ 2) (k2 + k3 * y) y := by
          have := ((hasDerivAt_id' y).const_mul k2).add ((hasDerivAt_pow 2 y).const_mul (k3 / 2))
          convert this using 1
          ring
        rw [deriv_fun_sub ((hD 1 (by norm_num)) y) (hg y), hgd.deriv, congrFun (hs 1) y,
          e2 y (Set.Ioo_subset_Icc_self hy)]
        ring) h0 hx
    simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] at this
    linarith
  refine ⟨d 0, k1, k2 / 2, k3 / 6, fun x hx => ?_⟩
  have hg : Differentiable ℝ (fun y : ℝ => k1 * y + k2 / 2 * y ^ 2 + k3 / 6 * y ^ 3) := by
    fun_prop
  have hd0 : Differentiable ℝ d := by simpa using hD 0 (by norm_num)
  have := eq_of_deriv_eq_zero_on_Ioo
    (f := fun y => d y - (k1 * y + k2 / 2 * y ^ 2 + k3 / 6 * y ^ 3))
    (hd0.sub hg) (fun y hy => by
      have hgd : HasDerivAt (fun y : ℝ => k1 * y + k2 / 2 * y ^ 2 + k3 / 6 * y ^ 3)
          (k1 + k2 * y + k3 / 2 * y ^ 2) y := by
        have := (((hasDerivAt_id' y).const_mul k1).add
          ((hasDerivAt_pow 2 y).const_mul (k2 / 2))).add
          ((hasDerivAt_pow 3 y).const_mul (k3 / 6))
        convert this using 1
        ring
      rw [deriv_fun_sub (hd0 y) (hg y), hgd.deriv, ← iteratedDeriv_one,
        e1 y (Set.Ioo_subset_Icc_self hy)]
      ring) h0 hx
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at this
  linarith

end MathlibExt.Analysis.Calculus.ZeroFourthDerivative

end
