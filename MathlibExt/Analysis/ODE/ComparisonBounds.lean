/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Scalar comparison bounds for linear decay and drift

Comparison estimates on `[0, t]` for real functions with two-sided derivatives, shared by the
uniform quasi-steady-state bounds for irreversible and reversible Michaelis–Menten kinetics.

## Main results

* `le_of_lt_on_eq`: if `f(0) ≤ B(0)` and `f' < B'` wherever `f = B` on `[0, T)`, then
  `f ≤ B` on `[0, T]` (Mathlib's `image_le_of_deriv_right_lt_deriv_boundary'` with
  two-sided derivatives).
* `le_of_decay`, `abs_le_of_decay`: if `w' = -a w + g` with `a ≥ λ > 0` and `g ≤ G`
  (resp. `|g| ≤ G`), then `w(t) ≤ |w(0)| e^{-λ t} + G/λ` (resp. `|w(t)| ≤ …`).
* `le_of_drift`, `abs_le_of_drift`: if `d' ≤ h` wherever `d ≥ 0` (and `-d' ≤ h` wherever
  `d ≤ 0` for the two-sided form), with `H' = h`, `H(0) = 0` and `H ≥ 0`, then
  `d(t) ≤ |d(0)| + H(t)` (resp. `|d(t)| ≤ …`).
-/

@[expose] public section

open Real Set

namespace MathlibExt.Analysis.ODE.ComparisonBounds

/-- Strict-boundary comparison on `[0, T]` for functions with two-sided derivatives. -/
theorem le_of_lt_on_eq {f f' B B' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (hB : ∀ t ∈ Icc 0 T, HasDerivAt B (B' t) t)
    (h0 : f 0 ≤ B 0) (hbd : ∀ t ∈ Ico 0 T, f t = B t → f' t < B' t) :
    ∀ t ∈ Icc 0 T, f t ≤ B t :=
  image_le_of_deriv_right_lt_deriv_boundary'
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt) h0
    (fun t ht ↦ (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hbd

/-- One-sided decay estimate: if `w' = -a w + g` with `a ≥ λ > 0` and `g ≤ G`, then
`w(t) ≤ |w(0)| e^{-λ t} + G/λ`. -/
theorem le_of_decay {w a g : ℝ → ℝ} {lam G : ℝ} (hlam : 0 < lam) (hG : 0 ≤ G)
    (hw : ∀ t, 0 ≤ t → HasDerivAt w (-a t * w t + g t) t)
    (ha : ∀ t, 0 ≤ t → lam ≤ a t) (hg : ∀ t, 0 ≤ t → g t ≤ G) {t : ℝ} (ht : 0 ≤ t) :
    w t ≤ |w 0| * exp (-lam * t) + G / lam := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  refine le_of_lt_on_eq (T := t) (f := w) (f' := fun r ↦ -a r * w r + g r)
    (B := fun r ↦ |w 0| * exp (-lam * r) + G / lam + δ)
    (B' := fun r ↦ |w 0| * (exp (-lam * r) * (-lam * 1)))
    (fun r hr ↦ hw r hr.1)
    (fun r _ ↦ (((((hasDerivAt_id' r).const_mul (-lam)).exp).const_mul |w 0|).add_const
      (G / lam)).add_const δ)
    (by simp only [mul_zero, exp_zero, mul_one]
        linarith [le_abs_self (w 0), div_nonneg hG hlam.le]) ?_ t ⟨ht, le_rfl⟩
  intro r hr heq
  have hwpos : 0 ≤ w r := by rw [heq]; positivity
  have h1 : -a r * w r ≤ -lam * w r := by nlinarith [ha r hr.1]
  have h2 := hg r hr.1
  have h3 : |w 0| * (exp (-lam * r) * (-lam * 1)) = -lam * w r + G + lam * δ := by
    rw [heq]; field_simp; ring
  rw [h3]
  nlinarith [mul_pos hlam hδ]

/-- Two-sided decay estimate: if `w' = -a w + g` with `a ≥ λ > 0` and `|g| ≤ G`, then
`|w(t)| ≤ |w(0)| e^{-λ t} + G/λ`. -/
theorem abs_le_of_decay {w a g : ℝ → ℝ} {lam G : ℝ} (hlam : 0 < lam)
    (hw : ∀ t, 0 ≤ t → HasDerivAt w (-a t * w t + g t) t)
    (ha : ∀ t, 0 ≤ t → lam ≤ a t) (hg : ∀ t, 0 ≤ t → |g t| ≤ G) {t : ℝ} (ht : 0 ≤ t) :
    |w t| ≤ |w 0| * exp (-lam * t) + G / lam := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 le_rfl)
  rw [abs_le]
  constructor
  · have := le_of_decay (w := fun r ↦ -w r) (a := a) (g := fun r ↦ -g r) hlam hG
      (fun r hr ↦ (hw r hr).neg.congr_deriv (by ring)) ha
      (fun r hr ↦ (neg_le_abs _).trans (hg r hr)) ht
    simp only [abs_neg] at this
    linarith
  · exact le_of_decay hlam hG hw ha (fun r hr ↦ (le_abs_self _).trans (hg r hr)) ht

/-- One-sided drift estimate: if `d' ≤ h` wherever `d ≥ 0`, and `H' = h`, `H(0) = 0`,
`H ≥ 0`, then `d(t) ≤ |d(0)| + H(t)`. -/
theorem le_of_drift {d d' H h : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt d (d' t) t) (hH : ∀ t, 0 ≤ t → HasDerivAt H (h t) t)
    (hH0 : H 0 = 0) (hHnn : ∀ t, 0 ≤ t → 0 ≤ H t)
    (hbd : ∀ t, 0 ≤ t → 0 ≤ d t → d' t ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    d t ≤ |d 0| + H t := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ := ε / (t + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδt : δ * t ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have key := le_of_lt_on_eq (T := t) (f := d) (f' := d')
    (B := fun r ↦ |d 0| + H r + δ * r) (B' := fun r ↦ h r + δ * 1)
    (fun r hr ↦ hd r hr.1)
    (fun r hr ↦ ((hH r hr.1).const_add |d 0|).add ((hasDerivAt_id' r).const_mul δ))
    (by simp only [hH0, mul_zero, add_zero]; exact le_abs_self _) ?_ t ⟨ht, le_rfl⟩
  · linarith
  · intro r hr heq
    have : 0 ≤ d r := by
      rw [heq]; have := hHnn r hr.1; have := abs_nonneg (d 0); nlinarith [hr.1]
    linarith [hbd r hr.1 this]

/-- Two-sided drift estimate. -/
theorem abs_le_of_drift {d d' H h : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt d (d' t) t) (hH : ∀ t, 0 ≤ t → HasDerivAt H (h t) t)
    (hH0 : H 0 = 0) (hHnn : ∀ t, 0 ≤ t → 0 ≤ H t)
    (hbd : ∀ t, 0 ≤ t → 0 ≤ d t → d' t ≤ h t)
    (hbd' : ∀ t, 0 ≤ t → d t ≤ 0 → -d' t ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    |d t| ≤ |d 0| + H t := by
  rw [abs_le]
  constructor
  · have := le_of_drift (d := fun r ↦ -d r) (d' := fun r ↦ -d' r) (fun r hr ↦ (hd r hr).neg)
      hH hH0 hHnn (fun r hr hr' ↦ hbd' r hr (by simpa using hr')) ht
    simp only [abs_neg] at this
    linarith
  · exact le_of_drift hd hH hH0 hHnn hbd ht

end MathlibExt.Analysis.ODE.ComparisonBounds
