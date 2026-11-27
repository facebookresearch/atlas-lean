/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Second-order continuous stirred-tank reactor

The exact perturbation equation and explicit profile for a quadratic reaction term.

## i. Overview

In a constant-density stirred tank with quadratic consumption, shifting the concentration by a
positive equilibrium leaves a linear decay term and an exact quadratic remainder. The explicit
profile solves this scalar equation whenever its denominator is nonzero.

## ii. Key results

- `Engineering.Process.CSTR.second_order_linearization` gives the exact shift, forward-time
  decay and error bound, and the finite-time denominator-zero criterion.

## iii. Table of contents

- A. Exact perturbation and forward-time behavior

## iv. References

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*,
  2nd ed., seventh printing, Equation 4.37 (p. 128), for the constant-volume balance.
-/

open Filter
open scoped Topology

namespace Engineering.Process.CSTR

/-! ## A. Exact perturbation and forward-time behavior -/

private theorem exp_decay_pos_le_one (rate t : ℝ) (hrate : 0 < rate) (ht : 0 ≤ t) :
    0 < Real.exp (-rate * t) ∧ Real.exp (-rate * t) ≤ 1 :=
  ⟨Real.exp_pos _,
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate.le) ht)⟩

private theorem perturbation_hasDerivAt (rate k d t : ℝ) (hrate : rate ≠ 0)
    (hden : 1 + (k * d / rate) * (1 - Real.exp (-rate * t)) ≠ 0) :
    let e (s : ℝ) := Real.exp (-rate * s)
    let δ (s : ℝ) := d * e s / (1 + (k * d / rate) * (1 - e s))
    HasDerivAt δ (-rate * δ t - k * (δ t) ^ 2) t := by
  dsimp only
  have he : HasDerivAt (fun s : ℝ => Real.exp (-rate * s)) (Real.exp (-rate * t) * -rate) t := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul (-rate)).exp
  have hd := ((he.const_sub 1).const_mul (k * d / rate)).const_add 1
  have hq := (he.const_mul d).fun_div hd hden
  convert hq using 1
  field_simp [hrate, hden]

/-- **Exact linearization remainder for a second-order stirred tank.** Let $D,k,c^*>0$ and
$c_{\mathrm{in}}\ge0$ with $D(c_{\mathrm{in}}-c^*)=k(c^*)^2$. Substituting $c=c^*+\delta$
into the concentration equation gives $\delta'=-\lambda\delta-k\delta^2$ exactly, where
$\lambda=D+2kc^*$. For initial deviation $d$, put $e(t)=\exp(-\lambda t)$,
$B(t)=1+(kd/\lambda)(1-e(t))$, and $u(t)=d e(t)/B(t)$. If $d>-\lambda/k$, then $B$ is
positive for all $t\ge0$, $u(0)=d$, $u$ solves the deviation equation there, and $u$ tends to
zero as $t\to+\infty$. This includes every positive $d$ and every physical initial concentration
$c^*+d\ge0$. For the sufficient margin $|d|<\lambda/k$, $B(t)\ge1-k|d|/\lambda>0$ and
$|u(t)|\le |d|e(t)/(1-k|d|/\lambda)$ for $t\ge0$. The denominator vanishes at some nonnegative
time exactly when $d<-\lambda/k$, which is outside the physical initial states.

Source: Rawlings and Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd ed.,
7th printing, Equation 4.37 (p. 128) for the balance; the quadratic remainder and profile are
derived for reaction term $-kc^2$. -/
public theorem second_order_linearization (D k cin cstar d : ℝ) (hD : 0 < D) (hk : 0 < k)
    (hcstar : 0 < cstar) (_hcin : 0 ≤ cin) (heq : D * (cin - cstar) = k * cstar ^ 2) :
    let rate := D + 2 * k * cstar
    let e (t : ℝ) := Real.exp (-rate * t)
    let B (t : ℝ) := 1 + (k * d / rate) * (1 - e t)
    let u (t : ℝ) := d * e t / B t
    (∀ δ : ℝ, D * (cin - (cstar + δ)) - k * (cstar + δ) ^ 2 = -rate * δ - k * δ ^ 2) ∧
    (0 ≤ cstar + d → -rate / k < d) ∧
    (-rate / k < d → u 0 = d ∧ (∀ t : ℝ, 0 ≤ t → 0 < B t ∧
      HasDerivAt u (-rate * u t - k * (u t) ^ 2) t) ∧ Tendsto u atTop (𝓝 0)) ∧
    (|d| < rate / k → 0 < 1 - k * |d| / rate ∧ ∀ t : ℝ, 0 ≤ t →
      1 - k * |d| / rate ≤ B t ∧ |u t| ≤ |d| * e t / (1 - k * |d| / rate)) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ B t = 0) ↔ d < -rate / k) := by
  let rate := D + 2 * k * cstar
  let a := k * d / rate
  let e (t : ℝ) := Real.exp (-rate * t)
  let B (t : ℝ) := 1 + a * (1 - e t)
  let u (t : ℝ) := d * e t / B t
  change (∀ δ : ℝ, D * (cin - (cstar + δ)) - k * (cstar + δ) ^ 2 = -rate * δ - k * δ ^ 2) ∧
    (0 ≤ cstar + d → -rate / k < d) ∧
    (-rate / k < d → u 0 = d ∧ (∀ t : ℝ, 0 ≤ t → 0 < B t ∧
      HasDerivAt u (-rate * u t - k * (u t) ^ 2) t) ∧ Tendsto u atTop (𝓝 0)) ∧
    (|d| < rate / k → 0 < 1 - k * |d| / rate ∧ ∀ t : ℝ, 0 ≤ t →
      1 - k * |d| / rate ≤ B t ∧ |u t| ≤ |d| * e t / (1 - k * |d| / rate)) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ B t = 0) ↔ d < -rate / k)
  have hrate : 0 < rate := by dsimp [rate]; positivity
  have hposB (ha : -1 ≤ a) (t : ℝ) (ht : 0 ≤ t) : 0 < B t := by
    obtain ⟨he, he₁⟩ : 0 < e t ∧ e t ≤ 1 := exp_decay_pos_le_one rate t hrate ht
    have hh := mul_nonneg (show 0 ≤ 1 + a by linarith) (sub_nonneg.mpr he₁)
    dsimp only [B]
    nlinarith only [he, hh]
  have hnegadm : -rate / k < d ↔ -1 < a := by
    dsimp only [a]
    rw [div_lt_iff₀ hk, lt_div_iff₀ hrate]
    simp only [neg_one_mul, mul_comm]
  have hneglt : d < -rate / k ↔ a < -1 := by
    dsimp only [a]
    rw [lt_div_iff₀ hk, div_lt_iff₀ hrate]
    simp only [neg_one_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro δ
    dsimp only [rate]
    linear_combination heq
  · intro hd
    apply (div_lt_iff₀ hk).mpr
    dsimp only [rate]
    nlinarith only [mul_nonneg hd hk.le, mul_pos hcstar hk, hD]
  · intro hd
    have ha := hnegadm.mp hd
    refine ⟨by simp [u, B, e], ?_, ?_⟩
    · intro t ht
      have hb := hposB ha.le t ht
      exact ⟨hb, perturbation_hasDerivAt rate k d t hrate.ne' hb.ne'⟩
    · have he : Tendsto e atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hrate))
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have ha' : Tendsto (fun _ : ℝ => a) atTop (𝓝 a) := tendsto_const_nhds
      have hd' : Tendsto (fun _ : ℝ => d) atTop (𝓝 d) := tendsto_const_nhds
      have hb : Tendsto B atTop (𝓝 (1 + a)) := by
        simpa only [B, sub_zero, mul_one] using hone.add (ha'.mul (hone.sub he))
      have hlim : Tendsto (fun t => d * e t / B t) atTop (𝓝 (d * 0 / (1 + a))) :=
        (hd'.mul he).div hb (by linarith)
      simpa only [u, mul_zero, zero_div] using hlim
  · intro hd
    have hmul := (lt_div_iff₀ hk).mp hd
    have hsmall : k * |d| / rate < 1 := (div_lt_iff₀ hrate).mpr (by simpa [mul_comm] using hmul)
    have hm : 0 < 1 - k * |d| / rate := sub_pos.mpr hsmall
    refine ⟨hm, ?_⟩
    intro t ht
    obtain ⟨he, he₁⟩ : 0 < e t ∧ e t ≤ 1 := exp_decay_pos_le_one rate t hrate ht
    have habs : |a| = k * |d| / rate := by rw [show a = k * d / rate by rfl, abs_div, abs_mul,
      abs_of_pos hk, abs_of_pos hrate]
    have hl := mul_le_mul_of_nonneg_right (neg_abs_le a) (sub_nonneg.mpr he₁)
    have hu := mul_nonneg (abs_nonneg a) he.le
    have hb : 1 - k * |d| / rate ≤ B t := by
      rw [← habs]
      dsimp only [B]
      nlinarith only [hl, hu]
    have hb' := lt_of_lt_of_le hm hb
    refine ⟨hb, ?_⟩
    rw [show u t = d * e t / B t by rfl, abs_div, abs_mul, abs_of_pos he, abs_of_pos hb']
    exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg d) he.le) hm hb
  · constructor
    · rintro ⟨t, ht, hzero⟩
      apply hneglt.mpr
      by_contra hn
      exact (hposB (le_of_not_gt hn) t ht).ne' hzero
    · intro hd
      have ha := hneglt.mp hd
      let r := 1 + 1 / a
      have hr₀ : 0 < r := by
        dsimp only [r]
        have hi : -1 < 1 / a := (lt_div_iff_of_neg (show a < 0 by linarith)).mpr (by linarith)
        linarith
      have hr₁ : r ≤ 1 := by
        dsimp only [r]
        have hi : 1 / a ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
        linarith
      let t := -Real.log r / rate
      have ht : 0 ≤ t := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hr₀.le hr₁)) hrate.le
      have he : e t = r := by
        dsimp only [e, t]
        rw [show -rate * (-Real.log r / rate) = Real.log r by field_simp [hrate.ne'],
          Real.exp_log hr₀]
      refine ⟨t, ht, ?_⟩
      dsimp only [B]
      rw [he]
      dsimp only [r]
      field_simp [show a ≠ 0 by linarith]
      ring

end Engineering.Process.CSTR
