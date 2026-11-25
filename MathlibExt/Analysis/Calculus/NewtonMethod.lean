/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Local convergence of Newton's method

This file proves quadratic convergence of Newton iteration near a simple real root.  It also
provides a one-step error estimate under a Lipschitz bound on the derivative.
-/

@[expose] public section

namespace MetaMathlibExt

open Set

private theorem newton_exists_mean_value_point
    {f : ℝ → ℝ} {c x : ℝ} (hf : Differentiable ℝ f) (hc : f c = 0) :
    ∃ ξ ∈ uIcc c x, f x = deriv f ξ * (x - c) ∧ |x - ξ| ≤ |x - c| := by
  by_cases hxc : x = c
  · subst x
    exact ⟨c, left_mem_uIcc, by simp [hc], by simp⟩
  rcases lt_or_gt_of_ne hxc with hxc_lt | hcx_lt
  · obtain ⟨ξ, hξ, hξ_slope⟩ :=
      exists_deriv_eq_slope f hxc_lt hf.continuous.continuousOn hf.differentiableOn
    have hfc_sub : f c - f x = deriv f ξ * (c - x) := by
      calc
        f c - f x = (f c - f x) / (c - x) * (c - x) := by
          symm
          exact div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hxc))
        _ = deriv f ξ * (c - x) := by rw [hξ_slope]
    have hfx_sub : f x - f c = deriv f ξ * (x - c) := by
      calc
        f x - f c = -(f c - f x) := by ring
        _ = -(deriv f ξ * (c - x)) := by rw [hfc_sub]
        _ = deriv f ξ * (x - c) := by ring
    refine ⟨ξ, ?_, ?_, ?_⟩
    · rw [uIcc_of_ge hxc_lt.le]
      exact ⟨hξ.1.le, hξ.2.le⟩
    · simpa [hc] using hfx_sub
    · rw [abs_of_nonpos (sub_nonpos.mpr hξ.1.le),
        abs_of_nonpos (sub_nonpos.mpr hxc_lt.le)]
      linarith [hξ.2]
  · obtain ⟨ξ, hξ, hξ_slope⟩ :=
      exists_deriv_eq_slope f hcx_lt hf.continuous.continuousOn hf.differentiableOn
    have hfx_sub : f x - f c = deriv f ξ * (x - c) := by
      calc
        f x - f c = (f x - f c) / (x - c) * (x - c) := by
          symm
          exact div_mul_cancel₀ _ (sub_ne_zero.mpr hxc)
        _ = deriv f ξ * (x - c) := by rw [hξ_slope]
    refine ⟨ξ, ?_, ?_, ?_⟩
    · rw [uIcc_of_le hcx_lt.le]
      exact ⟨hξ.1.le, hξ.2.le⟩
    · simpa [hc] using hfx_sub
    · rw [abs_of_nonneg (sub_nonneg.mpr hξ.2.le),
        abs_of_nonneg (sub_nonneg.mpr hcx_lt.le)]
      linarith [hξ.1]

/-- **One-step error bound for Newton's method.** Let $f : \mathbb{R} \to \mathbb{R}$ be
differentiable with $f(c) = 0$, let $x \in \mathbb{R}$, let $m > 0$ and let $K \ge 0$. If $f'$ is
Lipschitz with constant $K$ on the closed interval between $c$ and $x$ and $m \le |f'(x)|$,
then the Newton step from $x$ satisfies
$\left| x - f(x) / f'(x) - c \right| \le (K / m)\, |x - c|^2$. -/
theorem newton_step_sub_root_abs_le
    {f : ℝ → ℝ} {c x m : ℝ} {K : NNReal}
    (hf : Differentiable ℝ f) (hc : f c = 0) (hm : 0 < m)
    (hK : LipschitzOnWith K (deriv f) (uIcc c x))
    (hderiv : m ≤ |deriv f x|) :
    |x - f x / deriv f x - c| ≤ ((K : ℝ) / m) * |x - c| ^ 2 := by
  by_cases hxc : x = c
  · simp [hxc, hc]
  have hderiv_ne : deriv f x ≠ 0 := abs_pos.mp (hm.trans_le hderiv)
  obtain ⟨ξ, hξ_mem, hfx, hdist⟩ := newton_exists_mean_value_point hf hc (x := x)
  have hx_mem : x ∈ uIcc c x := right_mem_uIcc
  have hderiv_diff : |deriv f x - deriv f ξ| ≤ (K : ℝ) * |x - c| := by
    calc
      |deriv f x - deriv f ξ| ≤ (K : ℝ) * |x - ξ| := by
        simpa only [Real.dist_eq] using hK.dist_le_mul x hx_mem ξ hξ_mem
      _ ≤ (K : ℝ) * |x - c| :=
        mul_le_mul_of_nonneg_left hdist K.coe_nonneg
  have herror :
      x - f x / deriv f x - c =
        (deriv f x - deriv f ξ) * (x - c) / deriv f x := by
    rw [hfx]
    field_simp [hderiv_ne]
    ring
  rw [herror, abs_div, abs_mul]
  calc
    |deriv f x - deriv f ξ| * |x - c| / |deriv f x| ≤
        ((K : ℝ) * |x - c|) * |x - c| / |deriv f x| :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hderiv_diff (abs_nonneg _)) (abs_nonneg _)
    _ ≤ ((K : ℝ) * |x - c|) * |x - c| / m := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hm
      · exact hderiv
    _ = ((K : ℝ) / m) * |x - c| ^ 2 := by ring

private theorem newton_exists_neighborhood
    {f : ℝ → ℝ} {c : ℝ} (hf : ContDiff ℝ 2 f) (hderiv : deriv f c ≠ 0) :
    ∃ r > 0, ∃ m > 0, ∃ K : NNReal,
      (∀ x ∈ Icc (c - r) (c + r), m ≤ |deriv f x|) ∧
        LipschitzOnWith K (deriv f) (Icc (c - r) (c + r)) := by
  have hm : 0 < |deriv f c| / 2 := half_pos (abs_pos.mpr hderiv)
  have hcont : ContinuousAt (deriv f) c :=
    (hf.continuous_deriv (by norm_num)).continuousAt
  obtain ⟨ε, hε, hclose⟩ := (Metric.continuousAt_iff.mp hcont) _ hm
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hbound : ∀ x ∈ Icc (c - r) (c + r), |deriv f c| / 2 ≤ |deriv f x| := by
    intro x hx
    have hxc : |x - c| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hdist : dist x c < ε := by
      rw [Real.dist_eq]
      dsimp [r] at hxc
      linarith
    have hnear : |deriv f x - deriv f c| < |deriv f c| / 2 := by
      simpa only [Real.dist_eq] using hclose hdist
    have habs_diff : |deriv f c| - |deriv f x| ≤
        |deriv f x - deriv f c| := by
      simpa only [abs_sub_comm] using
        abs_sub_abs_le_abs_sub (deriv f c) (deriv f x)
    linarith
  have hderiv_contDiff : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨K, hK⟩ :=
    (hderiv_contDiff.contDiffOn (s := Icc (c - r) (c + r))).exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ⟨r, hr, |deriv f c| / 2, hm, K, hbound, hK⟩

private theorem newton_invariant_and_convergence
    {X : ℕ → ℝ} {c δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hδC : δ ≤ 1 / (2 * C)) (hX0 : |X 0 - c| < δ)
    (hquad : ∀ n, |X n - c| < δ →
      |X (n + 1) - c| ≤ C * |X n - c| ^ 2) :
    (∀ n, |X n - c| < δ) ∧
      (∀ n, |X (n + 1) - c| ≤ C * |X n - c| ^ 2) ∧
        Filter.Tendsto X Filter.atTop (nhds c) := by
  have hhalf : ∀ {e : ℝ}, 0 ≤ e → e < δ → C * e ^ 2 ≤ (1 / 2 : ℝ) * e := by
    intro e he heδ
    have he_limit : e ≤ 1 / (2 * C) := heδ.le.trans hδC
    have hCe : C * e ≤ (1 / 2 : ℝ) := by
      calc
        C * e ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left he_limit hC.le
        _ = (1 / 2 : ℝ) := by
          field_simp [ne_of_gt hC]
    calc
      C * e ^ 2 = (C * e) * e := by ring
      _ ≤ (1 / 2 : ℝ) * e := mul_le_mul_of_nonneg_right hCe he
  have hstay : ∀ n, |X n - c| < δ := by
    intro n
    induction n with
    | zero => exact hX0
    | succ n ihn =>
        have hstep : |X (n + 1) - c| ≤ (1 / 2 : ℝ) * |X n - c| :=
          (hquad n ihn).trans (hhalf (abs_nonneg _) ihn)
        have hstrict : (1 / 2 : ℝ) * |X n - c| < δ := by
          calc
            (1 / 2 : ℝ) * |X n - c| < (1 / 2 : ℝ) * δ := by
              exact mul_lt_mul_of_pos_left ihn (by norm_num)
            _ < δ := by linarith
        simpa only [Nat.succ_eq_add_one] using hstep.trans_lt hstrict
  have hgeom : ∀ n, |X n - c| ≤ (1 / 2 : ℝ) ^ n * |X 0 - c| := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
        have hstep : |X (n + 1) - c| ≤ (1 / 2 : ℝ) * |X n - c| :=
          (hquad n (hstay n)).trans (hhalf (abs_nonneg _) (hstay n))
        calc
          |X (Nat.succ n) - c| = |X (n + 1) - c| := by rw [Nat.succ_eq_add_one]
          _ ≤ (1 / 2 : ℝ) * |X n - c| := hstep
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * |X 0 - c|) :=
            mul_le_mul_of_nonneg_left ihn (by norm_num)
          _ = (1 / 2 : ℝ) ^ Nat.succ n * |X 0 - c| := by
            rw [pow_succ]
            ring
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hupper : Filter.Tendsto (fun n => (1 / 2 : ℝ) ^ n * |X 0 - c|)
      Filter.atTop (nhds 0) := by
    simpa using hpow.mul_const |X 0 - c|
  have habs : Filter.Tendsto (fun n => |X n - c|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hgeom hupper
  refine ⟨hstay, fun n => hquad n (hstay n), ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using habs

/-- **Local quadratic convergence of Newton's method.** Let $f : \mathbb{R} \to \mathbb{R}$ be twice
continuously differentiable and let $c$ be a simple root of $f$: $f(c) = 0$ and $f'(c) \ne 0$.
Then there exist $\delta > 0$ and a real constant $C$ with the following property. For every
$x_0 \in (c - \delta, c + \delta)$ and every real sequence $(x_n)$ that starts at $x_0$ and
satisfies $x_{n+1} = x_n - f(x_n) / f'(x_n)$ for all $n$, every $x_n$ lies in
$(c - \delta, c + \delta)$, $|x_{n+1} - c| \le C\, |x_n - c|^2$ for all $n$, and $x_n \to c$.

Proof: Continuity keeps $f'$ away from zero near $c$, and $C^2$ regularity makes $f'$ Lipschitz
on a compact interval around $c$. The mean value theorem then bounds one Newton step by
$(K / m)\, |x - c|^2$, where $m > 0$ bounds $|f'|$ from below and $K$ is a Lipschitz constant
of $f'$; this replaces the Lagrange remainder in Wikipedia's "Proof of quadratic convergence
for Newton's iterative method". Shrinking the neighborhood gives an invariant half-contraction
and geometric convergence.

Proves `Wanted` entry `newton_method_local_quadratic_convergence`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entries `Newton's method` and `rate of convergence and estimation of error`
(unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed.,
Theorem 2.6;
stable ref https://en.wikipedia.org/wiki/Newton%27s_method.
-/
theorem newton_method_local_quadratic_convergence
    {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ 2 f) (hc : f c = 0) (hderiv : deriv f c ≠ 0) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x₀ ∈ Set.Ioo (c - δ) (c + δ),
      ∀ X : ℕ → ℝ, X 0 = x₀ →
        (∀ n, X (n + 1) = X n - f (X n) / deriv f (X n)) →
        (∀ n, X n ∈ Set.Ioo (c - δ) (c + δ)) ∧
        (∀ n, |X (n + 1) - c| ≤ C * |X n - c| ^ 2) ∧
        Filter.Tendsto X Filter.atTop (nhds c) := by
  obtain ⟨r, hr, m, hm, K, hderiv_lower, hK⟩ :=
    newton_exists_neighborhood hf hderiv
  let C : ℝ := (K : ℝ) / m + 1
  have hC : 0 < C := by
    dsimp [C]
    have hnonneg : 0 ≤ (K : ℝ) / m := div_nonneg K.coe_nonneg hm.le
    linarith
  let δ : ℝ := min r (1 / (2 * C))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hr (one_div_pos.mpr (mul_pos (by norm_num) hC))
  have hδr : δ ≤ r := by
    dsimp [δ]
    exact min_le_left _ _
  have hδC : δ ≤ 1 / (2 * C) := by
    dsimp [δ]
    exact min_le_right _ _
  refine ⟨δ, hδ, C, ?_⟩
  intro x₀ hx₀ X hX₀ hrec
  have hx₀_abs : |x₀ - c| < δ := by
    rw [abs_lt]
    exact ⟨by linarith [hx₀.1], by linarith [hx₀.2]⟩
  have hX₀_abs : |X 0 - c| < δ := by simpa only [hX₀] using hx₀_abs
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hquad : ∀ n, |X n - c| < δ →
      |X (n + 1) - c| ≤ C * |X n - c| ^ 2 := by
    intro n hn
    have hXr : |X n - c| ≤ r := hn.le.trans hδr
    have hX_mem : X n ∈ Icc (c - r) (c + r) := by
      rw [abs_le] at hXr
      exact ⟨by linarith [hXr.1], by linarith [hXr.2]⟩
    have hc_mem : c ∈ Icc (c - r) (c + r) := by
      exact ⟨by linarith, by linarith⟩
    have hsub : uIcc c (X n) ⊆ Icc (c - r) (c + r) := by
      intro y hy
      rcases mem_uIcc.mp hy with hcy | hyc
      · exact ⟨hc_mem.1.trans hcy.1, hcy.2.trans hX_mem.2⟩
      · exact ⟨hX_mem.1.trans hyc.1, hyc.2.trans hc_mem.2⟩
    have hstep := newton_step_sub_root_abs_le hf_diff hc hm (hK.mono hsub)
      (hderiv_lower (X n) hX_mem)
    have hcoeff : (K : ℝ) / m ≤ C := by
      dsimp [C]
      linarith
    calc
      |X (n + 1) - c| = |X n - f (X n) / deriv f (X n) - c| := by rw [hrec n]
      _ ≤ ((K : ℝ) / m) * |X n - c| ^ 2 := hstep
      _ ≤ C * |X n - c| ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  obtain ⟨hstay, hquadratic, htendsto⟩ :=
    newton_invariant_and_convergence hδ hC hδC hX₀_abs hquad
  refine ⟨?_, hquadratic, htendsto⟩
  intro n
  have hn := hstay n
  rw [abs_lt] at hn
  exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

end MetaMathlibExt
