/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Landau–Kolmogorov inequality on the real line

For a twice continuously differentiable function `f : ℝ → ℝ` whose values and
second derivative are uniformly bounded, the first derivative is uniformly bounded by
`‖f'‖ ≤ √(2 ‖f‖ ‖f''‖)`, i.e. `(f' x)² ≤ 2 M₀ M₂` whenever `|f| ≤ M₀` and
`|f''| ≤ M₂` everywhere. This is the case `n = 2`, `k = 1` of the
Landau–Kolmogorov inequalities. The proof is Taylor's theorem with Lagrange
remainder at `x ± h`, subtracted to cancel the constant term, followed by
optimizing in `h`. A one-sided variant (using only `x + h`) gives the weaker
constant `4`. The complex-valued case follows by applying the real case to the
real and imaginary parts, with constant `4`.

This is a companion to the calculus / approximation material of
`v1/Atlas/IntroductionToFunctionalAnalysis`; it is not one of the 72 v1 targets.
-/

@[expose] public section

namespace MetaMathlibExt

open Set

/-- Taylor's theorem with Lagrange remainder, second order, in the form used below:
`f (x + h) = f x + h * f' x + (h² / 2) * f'' ξ` for some `ξ` strictly between
`x` and `x + h`. -/
private lemma taylor_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x h : ℝ) (hh : h ≠ 0) :
    ∃ ξ ∈ uIoo x (x + h),
      f (x + h) = f x + h * deriv f x + (h ^ 2 / 2) * deriv (deriv f) ξ := by
  obtain ⟨ξ, hξ, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x + h) (x₀ := x) (n := 1)
      (fun hcon => hh (by linarith [hcon])) (hf.contDiffOn)
  refine ⟨ξ, hξ, ?_⟩
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiable (by simp)).differentiableAt
  have hpoly : taylorWithinEval f 1 (uIcc x (x + h)) x (x + h)
      = f x + h * deriv f x := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one,
      hdiff.derivWithin
        ((uniqueDiffOn_uIcc (fun hcon => hh (by linarith [hcon]))).uniqueDiffWithinAt
          left_mem_uIcc)]
    simp [smul_eq_mul]
  have hiter : iteratedDeriv (1 + 1) f ξ = deriv (deriv f) ξ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hpoly, hiter] at heq
  have hpow : (x + h - x) ^ (1 + 1) = h ^ 2 := by ring
  have hfact : (Nat.factorial (1 + 1) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hpow, hfact] at heq
  linarith

/-- Two-sided difference estimate: `2 * h * |f' x| ≤ 2 * M₀ + h² * M₂`. -/
private lemma two_sided_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₂ : ∀ x, |deriv (deriv f) x| ≤ M₂)
    (x : ℝ) {h : ℝ} (hh : 0 < h) : 2 * h * |deriv f x| ≤ 2 * M₀ + h ^ 2 * M₂ := by
  obtain ⟨xiP, -, hP⟩ := taylor_two hf x h (ne_of_gt hh)
  obtain ⟨xiM, -, hM⟩ := taylor_two hf x (-h) (neg_ne_zero.mpr (ne_of_gt hh))
  have hcomb : 2 * h * deriv f x =
      (f (x + h) - f (x - h)) - (h ^ 2 / 2) * (deriv (deriv f) xiP - deriv (deriv f) xiM) := by
    have h₁ : x + -h = x - h := by ring
    rw [h₁] at hM
    have h₂ : (-h) ^ 2 = h ^ 2 := by ring
    rw [h₂] at hM
    linarith
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ x)
  have hM₂nn : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM₂ x)
  calc 2 * h * |deriv f x| = |2 * h * deriv f x| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * h)]
    _ = |(f (x + h) - f (x - h)) - (h ^ 2 / 2) * (deriv (deriv f) xiP - deriv (deriv f) xiM)| := by
        rw [hcomb]
    _ ≤ |f (x + h) - f (x - h)| + |(h ^ 2 / 2) * (deriv (deriv f) xiP - deriv (deriv f) xiM)| :=
        abs_sub _ _
    _ ≤ (|f (x + h)| + |f (x - h)|) +
          (h ^ 2 / 2) * (|deriv (deriv f) xiP| + |deriv (deriv f) xiM|) := by
        gcongr
        · exact abs_sub _ _
        · rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ 2 * M₀ + h ^ 2 * M₂ := by
        have e1 := hM₀ (x + h)
        have e2 := hM₀ (x - h)
        have e3 := hM₂ xiP
        have e4 := hM₂ xiM
        nlinarith [mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 2 by positivity) hM₂nn]

/-- One-sided estimate: `h * |f' x| ≤ 2 * M₀ + (h² / 2) * M₂`. -/
private lemma one_sided_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₂ : ∀ x, |deriv (deriv f) x| ≤ M₂)
    (x : ℝ) {h : ℝ} (hh : 0 < h) : h * |deriv f x| ≤ 2 * M₀ + (h ^ 2 / 2) * M₂ := by
  obtain ⟨ξ, -, hP⟩ := taylor_two hf x h (ne_of_gt hh)
  have hcomb : h * deriv f x =
      (f (x + h) - f x) - (h ^ 2 / 2) * deriv (deriv f) ξ := by linarith
  have hM₂nn : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM₂ x)
  calc h * |deriv f x| = |h * deriv f x| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ h)]
    _ = |(f (x + h) - f x) - (h ^ 2 / 2) * deriv (deriv f) ξ| := by rw [hcomb]
    _ ≤ |f (x + h) - f x| + |(h ^ 2 / 2) * deriv (deriv f) ξ| := abs_sub _ _
    _ ≤ (|f (x + h)| + |f x|) + (h ^ 2 / 2) * |deriv (deriv f) ξ| := by
        gcongr
        · exact abs_sub _ _
        · rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 2 * M₀ + (h ^ 2 / 2) * M₂ := by
        have e1 := hM₀ (x + h)
        have e2 := hM₀ x
        have e3 := hM₂ ξ
        nlinarith [mul_nonneg (show (0:ℝ) ≤ h ^ 2 / 2 by positivity) hM₂nn]

/-- If `a * h * |d| ≤ b * M₀` for every `h > 0` (with `a > 0`), then `d = 0`. -/
private lemma eq_zero_of_forall_mul_le {d a b M₀ : ℝ} (ha : 0 < a)
    (key : ∀ h : ℝ, 0 < h → a * h * |d| ≤ b * M₀) : d = 0 := by
  by_contra hd
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hnn : 0 ≤ b * M₀ := by
    have := key 1 one_pos
    have : 0 ≤ a * 1 * |d| := by positivity
    linarith
  set h := (b * M₀ + 1) / (a * |d|) with hhdef
  have hpos : 0 < h := by positivity
  have hk := key h hpos
  have hEq : a * h * |d| = b * M₀ + 1 := by
    rw [hhdef]
    field_simp
  linarith

/-- Optimization step: from `a * h * |d| ≤ b * M₀ + c * h² * M₂` for all `h > 0`,
minimizing over `h` gives `d² ≤ (4 * b * c / a²) * M₀ * M₂`. -/
private lemma sq_le_of_key {d M₀ M₂ a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hM₀ : 0 < M₀) (hM₂ : 0 < M₂)
    (key : ∀ h : ℝ, 0 < h → a * h * |d| ≤ b * M₀ + c * h ^ 2 * M₂) :
    d ^ 2 ≤ (4 * b * c / a ^ 2) * M₀ * M₂ := by
  set h := Real.sqrt (b * M₀ / (c * M₂)) with hhdef
  have hpos : 0 < h := by
    rw [hhdef]
    exact Real.sqrt_pos_of_pos (div_pos (mul_pos hb hM₀) (mul_pos hc hM₂))
  have hsq : h ^ 2 = b * M₀ / (c * M₂) :=
    Real.sq_sqrt (le_of_lt (div_pos (mul_pos hb hM₀) (mul_pos hc hM₂)))
  have hk := key h hpos
  rw [hsq] at hk
  have hbound : a * h * |d| ≤ 2 * b * M₀ := by
    have hcc : (c * (b * M₀ / (c * M₂))) * M₂ = b * M₀ := by field_simp
    nlinarith [hk]
  have habs : |d| ≤ (2 * b * M₀) / (a * h) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < a * h)]
    calc |d| * (a * h) = a * h * |d| := by ring
      _ ≤ 2 * b * M₀ := hbound
  calc d ^ 2 = |d| ^ 2 := (sq_abs d).symm
    _ ≤ ((2 * b * M₀) / (a * h)) ^ 2 := by
        have h1 : (0:ℝ) ≤ |d| := abs_nonneg _
        have h2 : (0:ℝ) ≤ (2 * b * M₀) / (a * h) := by positivity
        calc |d| ^ 2 = |d| * |d| := by ring
          _ ≤ ((2 * b * M₀) / (a * h)) * ((2 * b * M₀) / (a * h)) :=
              mul_le_mul habs habs h1 h2
          _ = ((2 * b * M₀) / (a * h)) ^ 2 := by ring
    _ = (4 * b * c / a ^ 2) * M₀ * M₂ := by
        have hden : (a * h) ^ 2 = a ^ 2 * (b * M₀ / (c * M₂)) := by rw [mul_pow, hsq]
        rw [div_pow, hden]
        field_simp
        ring

/-- **Landau–Kolmogorov inequality** on `ℝ` (case `n = 2`, `k = 1`): if `f` is twice
continuously differentiable with `|f| ≤ M₀` and `|f''| ≤ M₂` everywhere, then
`(f' x)² ≤ 2 * M₀ * M₂` for every `x`. -/
theorem landau_inequality {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₂ : ∀ x, |deriv (deriv f) x| ≤ M₂) (x : ℝ) :
    (deriv f x) ^ 2 ≤ 2 * M₀ * M₂ := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ x)
  have hM₂nn : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM₂ x)
  rcases eq_or_lt_of_le hM₀nn with hM₀z | hM₀pos
  · -- `M₀ = 0`: then `f = 0`, so `f' = 0`.
    have hf0 : f = fun _ => 0 := by
      funext y
      have h := hM₀ y
      rw [← hM₀z] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hder0 : (deriv (fun _ : ℝ => (0:ℝ)) x) ^ 2 = 0 := by rw [deriv_const]; norm_num
    rw [hf0, hder0]
    positivity
  rcases eq_or_lt_of_le hM₂nn with hM₂z | hM₂pos
  · -- `M₂ = 0`: the two-sided estimate forces `f' x = 0`.
    have key : ∀ h : ℝ, 0 < h → 2 * h * |deriv f x| ≤ 2 * M₀ := by
      intro h hh
      have := two_sided_bound hf hM₀ hM₂ x hh
      rw [← hM₂z] at this
      simpa using this
    have hd0 : deriv f x = 0 :=
      eq_zero_of_forall_mul_le (show (0:ℝ) < 2 by norm_num) key
    rw [hd0]
    norm_num
    positivity
  · have key : ∀ h : ℝ, 0 < h → 2 * h * |deriv f x| ≤ 2 * M₀ + 1 * h ^ 2 * M₂ := by
      intro h hh
      have := two_sided_bound hf hM₀ hM₂ x hh
      simpa using this
    have h := sq_le_of_key (d := deriv f x) (M₀ := M₀) (M₂ := M₂) (a := 2) (b := 2) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) hM₀pos hM₂pos key
    have hfactor : (4 * 2 * 1 / (2:ℝ) ^ 2) * M₀ * M₂ = 2 * M₀ * M₂ := by ring
    rwa [hfactor] at h

/-- Square-root form of the Landau–Kolmogorov inequality. -/
theorem landau_inequality_abs {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₂ : ∀ x, |deriv (deriv f) x| ≤ M₂) (x : ℝ) :
    |deriv f x| ≤ Real.sqrt (2 * M₀ * M₂) := by
  have h := landau_inequality hf hM₀ hM₂ x
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- One-sided Landau–Kolmogorov inequality (constant `4`): the same hypotheses give
`(f' x)² ≤ 4 * M₀ * M₂`. This is the form obtained from the one-sided Taylor
expansion; the two-sided argument sharpens the constant to `2`. -/
theorem landau_inequality_one_sided {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₂ : ∀ x, |deriv (deriv f) x| ≤ M₂) (x : ℝ) :
    (deriv f x) ^ 2 ≤ 4 * M₀ * M₂ := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ x)
  have hM₂nn : 0 ≤ M₂ := le_trans (abs_nonneg _) (hM₂ x)
  rcases eq_or_lt_of_le hM₀nn with hM₀z | hM₀pos
  · have hf0 : f = fun _ => 0 := by
      funext y
      have h := hM₀ y
      rw [← hM₀z] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hder0 : (deriv (fun _ : ℝ => (0:ℝ)) x) ^ 2 = 0 := by rw [deriv_const]; norm_num
    rw [hf0, hder0]
    positivity
  rcases eq_or_lt_of_le hM₂nn with hM₂z | hM₂pos
  · have key : ∀ h : ℝ, 0 < h → 1 * h * |deriv f x| ≤ 2 * M₀ := by
      intro h hh
      have hthis := one_sided_bound hf hM₀ hM₂ x hh
      rw [← hM₂z] at hthis
      simp only [mul_zero, add_zero] at hthis
      calc 1 * h * |deriv f x| = h * |deriv f x| := by ring
        _ ≤ 2 * M₀ := hthis
    have hd0 : deriv f x = 0 :=
      eq_zero_of_forall_mul_le (show (0:ℝ) < 1 by norm_num) key
    rw [hd0]
    norm_num
    positivity
  · have key : ∀ h : ℝ, 0 < h → 1 * h * |deriv f x| ≤ 2 * M₀ + (1 / 2) * h ^ 2 * M₂ := by
      intro h hh
      have := one_sided_bound hf hM₀ hM₂ x hh
      calc 1 * h * |deriv f x| = h * |deriv f x| := by ring
        _ ≤ 2 * M₀ + (h ^ 2 / 2) * M₂ := this
        _ = 2 * M₀ + (1 / 2) * h ^ 2 * M₂ := by ring
    have h := sq_le_of_key (d := deriv f x) (M₀ := M₀) (M₂ := M₂) (a := 1) (b := 2) (c := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) hM₀pos hM₂pos key
    have hfactor : (4 * 2 * (1 / 2 : ℝ) / (1:ℝ) ^ 2) * M₀ * M₂ = 4 * M₀ * M₂ := by ring
    rwa [hfactor] at h

/-- Derivative of a real linear functional applied to a differentiable function:
`deriv (fun y => L (g y)) x = L (deriv g x)` for `L : ℂ →L[ℝ] ℝ`. -/
private lemma deriv_clm_apply_const {g : ℝ → ℂ} {L : ℂ →L[ℝ] ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => L (g y)) x = L (deriv g x) := by
  have h := deriv_clm_apply (c := fun _ => L) (u := g) (differentiableAt_const L) hg
  simpa using h

/-- **Landau–Kolmogorov inequality, complex-valued case** (constant `4`): if
`f : ℝ → ℂ` is twice continuously differentiable with `‖f‖ ≤ M₀` and
`‖f''‖ ≤ M₂` everywhere, then `‖f' x‖² ≤ 4 * M₀ * M₂` for every `x`. The
constant `4` comes from applying the real inequality to the real and imaginary
parts and adding. -/
theorem landau_inequality_complex {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {M₀ M₂ : ℝ}
    (hM₀ : ∀ x, ‖f x‖ ≤ M₀) (hM₂ : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂) (x : ℝ) :
    ‖deriv f x‖ ^ 2 ≤ 4 * M₀ * M₂ := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hdiff' : Differentiable ℝ (deriv f) :=
    (ContDiff.deriv' (show ContDiff ℝ (1 + 1) f from hf)).differentiable (by simp)
  -- The real and imaginary parts are twice continuously differentiable.
  have hfre : ContDiff ℝ 2 (fun y => (f y).re) := by
    have hcomp : ContDiff ℝ 2 (Complex.reCLM ∘ f) := Complex.reCLM.contDiff.comp hf
    have hfun : (Complex.reCLM ∘ f) = fun y => (f y).re :=
      funext fun y => Complex.reCLM_apply (f y)
    rwa [hfun] at hcomp
  have hfim : ContDiff ℝ 2 (fun y => (f y).im) := by
    have hcomp : ContDiff ℝ 2 (Complex.imCLM ∘ f) := Complex.imCLM.contDiff.comp hf
    have hfun : (Complex.imCLM ∘ f) = fun y => (f y).im :=
      funext fun y => Complex.imCLM_apply (f y)
    rwa [hfun] at hcomp
  -- Derivatives of the parts are the parts of the derivatives, at every point.
  have hderiv_re : ∀ y : ℝ, deriv (fun z => (f z).re) y = (deriv f y).re := by
    intro y
    have h := deriv_clm_apply_const (L := Complex.reCLM) (hdiff.differentiableAt (x := y))
    have hfun : (fun z => Complex.reCLM (f z)) = fun z => (f z).re :=
      funext fun z => Complex.reCLM_apply (f z)
    rw [hfun] at h
    simpa [Complex.reCLM_apply] using h
  have hderiv_im : ∀ y : ℝ, deriv (fun z => (f z).im) y = (deriv f y).im := by
    intro y
    have h := deriv_clm_apply_const (L := Complex.imCLM) (hdiff.differentiableAt (x := y))
    have hfun : (fun z => Complex.imCLM (f z)) = fun z => (f z).im :=
      funext fun z => Complex.imCLM_apply (f z)
    rw [hfun] at h
    simpa [Complex.imCLM_apply] using h
  have hderiv2_re : ∀ y : ℝ,
      deriv (deriv (fun z => (f z).re)) y = (deriv (deriv f) y).re := by
    intro y
    have hfun : deriv (fun z => (f z).re) = fun z => (deriv f z).re :=
      funext fun z => hderiv_re z
    rw [hfun]
    have h := deriv_clm_apply_const (L := Complex.reCLM) (hdiff'.differentiableAt (x := y))
    have hfun₂ : (fun z => Complex.reCLM (deriv f z)) = fun z => (deriv f z).re :=
      funext fun z => Complex.reCLM_apply (deriv f z)
    rw [hfun₂] at h
    simpa [Complex.reCLM_apply] using h
  have hderiv2_im : ∀ y : ℝ,
      deriv (deriv (fun z => (f z).im)) y = (deriv (deriv f) y).im := by
    intro y
    have hfun : deriv (fun z => (f z).im) = fun z => (deriv f z).im :=
      funext fun z => hderiv_im z
    rw [hfun]
    have h := deriv_clm_apply_const (L := Complex.imCLM) (hdiff'.differentiableAt (x := y))
    have hfun₂ : (fun z => Complex.imCLM (deriv f z)) = fun z => (deriv f z).im :=
      funext fun z => Complex.imCLM_apply (deriv f z)
    rw [hfun₂] at h
    simpa [Complex.imCLM_apply] using h
  -- Bounds for the parts.
  have hM₀re : ∀ y, |(fun z => (f z).re) y| ≤ M₀ :=
    fun y => (Complex.abs_re_le_norm (f y)).trans (hM₀ y)
  have hM₀im : ∀ y, |(fun z => (f z).im) y| ≤ M₀ :=
    fun y => (Complex.abs_im_le_norm (f y)).trans (hM₀ y)
  have hM₂re : ∀ y, |deriv (deriv (fun z => (f z).re)) y| ≤ M₂ := by
    intro y
    rw [hderiv2_re y]
    exact (Complex.abs_re_le_norm _).trans (hM₂ y)
  have hM₂im : ∀ y, |deriv (deriv (fun z => (f z).im)) y| ≤ M₂ := by
    intro y
    rw [hderiv2_im y]
    exact (Complex.abs_im_le_norm _).trans (hM₂ y)
  have hre := landau_inequality hfre hM₀re hM₂re x
  have him := landau_inequality hfim hM₀im hM₂im x
  rw [hderiv_re x] at hre
  rw [hderiv_im x] at him
  have hnorm : ‖deriv f x‖ ^ 2 = (deriv f x).re ^ 2 + (deriv f x).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hnorm]
  linarith

end MetaMathlibExt
