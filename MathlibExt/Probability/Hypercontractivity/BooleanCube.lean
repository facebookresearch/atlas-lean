/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.BonamiTensorize
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Hypercontractivity Theorem on the Boolean cube

The proved library has the `(p, 2)` case `‖T_ρ f‖₂ ≤ ‖f‖_{1+ρ²}` of the Bonami–Beckner
inequality on the uniform cube (`StatMech.Probability.vtp_hypercontractivity`), its dual
`(2, 4)` case and the Bonami Lemma (`MathlibExt.Probability.Hypercontractivity.BonamiLemma`).
This module proves the full Hypercontractivity Theorem for all `1 ≤ p ≤ q < ∞`.

## Main statements

* `BooleanCube.hypercontractivity_theorem`: `‖T_ρ f‖_q ≤ ‖f‖_p` for
  `0 ≤ ρ ≤ √((p - 1)/(q - 1))`.

## References

* A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*, Ann. Inst. Fourier
  20 (1970), 335-402.
* W. Beckner, *Inequalities in Fourier analysis*, Ann. of Math. 102 (1975), 159-182.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 9 (introduction) and Chapter 10.
-/

@[expose] public section

namespace BooleanCube

open Real Set StatMech.Probability

-- Compare the endpoints by checking the derivative on the open interval.
private lemma compare_endpoints {a b : ℝ} {F : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ d, HasDerivAt F d x ∧ 0 ≤ d) : F a ≤ F b := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc _ _ (left_mem_Icc.mpr hab)
    (right_mem_Icc.mpr hab) hab
  · rw [interior_Icc]
    intro x hx
    obtain ⟨d, h, _⟩ := hd x hx
    exact h.differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    obtain ⟨d, h, hd⟩ := hd x hx
    rwa [h.deriv]

-- The tangent bound for the logarithm in the derivative of the two-point entropy.
private lemma log_ratio_le {s : ℝ} (hs : s ≤ 1) :
    log (2 / (1 + s ^ 2)) ≤ 1 - s := by
  let F (t : ℝ) := t - log ((1 + t ^ 2) / 2)
  have h := compare_endpoints (F := F) hs (by
    intro t _
    dsimp [F]
    fun_prop (disch := positivity)) <| by
    intro t _
    have ht : 0 < (1 + t ^ 2) / 2 := by positivity
    have hd := (hasDerivAt_id t).sub
      ((((hasDerivAt_pow 2 t).const_add 1).div_const 2).log ht.ne')
    refine ⟨_, hd, ?_⟩
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    nlinarith [sq_nonneg (t - 1)]
  simp [F, log_div (by positivity : 1 + s ^ 2 ≠ 0) two_ne_zero,
    log_div two_ne_zero (by positivity : 1 + s ^ 2 ≠ 0)] at *
  linarith

-- On two points the log-Sobolev inequality bounds twice the entropy of (x², y²) by (x-y)².
private lemma entropy_le_of_le {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    x ^ 2 * log (x ^ 2) + y ^ 2 * log (y ^ 2) -
      (x ^ 2 + y ^ 2) * log ((x ^ 2 + y ^ 2) / 2) ≤ (x - y) ^ 2 := by
  let F (t : ℝ) := (t - y) ^ 2 - t ^ 2 * log (t ^ 2) +
    (t ^ 2 + y ^ 2) * log ((t ^ 2 + y ^ 2) / 2)
  have h := compare_endpoints (F := F) hyx (by
    intro t ht
    have ht0 := hy.trans_le ht.1
    dsimp [F]
    fun_prop (disch := positivity)) <| by
    intro t ht
    have ht0 := hy.trans ht.1
    have hS : 0 < t ^ 2 + y ^ 2 := by positivity
    have hd := (((hasDerivAt_id t).sub_const y).pow 2).sub
      ((hasDerivAt_pow 2 t).mul ((hasDerivAt_pow 2 t).log (by positivity)))
    have hsum := (hasDerivAt_pow 2 t).add_const (y ^ 2)
    refine ⟨_, hd.add (hsum.mul ((hsum.div_const 2).log (by positivity))), ?_⟩
    have hl := log_ratio_le (s := y / t) ((div_le_one ht0).mpr ht.1.le)
    rw [show 2 / (1 + (y / t) ^ 2) = t ^ 2 / ((t ^ 2 + y ^ 2) / 2) by field_simp,
      log_div (by positivity) (by positivity)] at hl
    have hmul := mul_le_mul_of_nonneg_left hl ht0.le
    field_simp at hmul ⊢
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hmul) hS.le]
  have heq : (y ^ 2 + y ^ 2) / 2 = y ^ 2 := by ring
  dsimp [F] at h
  rw [heq] at h
  linarith

private lemma entropy_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 * log (x ^ 2) + y ^ 2 * log (y ^ 2) -
      (x ^ 2 + y ^ 2) * log ((x ^ 2 + y ^ 2) / 2) ≤ (x - y) ^ 2 := by
  rcases le_total y x with h | h
  · exact entropy_le_of_le hy h
  · simpa only [add_comm (y ^ 2) (x ^ 2), add_comm (y ^ 2 * _) (x ^ 2 * _), sub_sq_comm y x]
      using entropy_le_of_le hx h

-- Integrating the square of r * t^(r/2 - 1) - c gives the power-difference inequality.
private lemma power_gap_of_lt {x y r : ℝ} (hy : 0 < y) (hyx : y < x) (hr : 1 < r) :
    4 * (r - 1) * (x ^ (r / 2) - y ^ (r / 2)) ^ 2 ≤
      r ^ 2 * (x - y) * (x ^ (r - 1) - y ^ (r - 1)) := by
  let c := 2 * (x ^ (r / 2) - y ^ (r / 2)) / (x - y)
  let F (t : ℝ) := r ^ 2 / (r - 1) * t ^ (r - 1) - 4 * c * t ^ (r / 2) + c ^ 2 * t
  have h := compare_endpoints (F := F) hyx.le (by
    intro t ht
    have ht0 := hy.trans_le ht.1
    dsimp [F]
    fun_prop (disch := positivity)) <| by
    intro t ht
    have ht0 := hy.trans ht.1
    refine ⟨(r * t ^ (r / 2 - 1) - c) ^ 2, ?_, sq_nonneg _⟩
    convert! ((((hasDerivAt_rpow_const (p := r - 1) (Or.inl ht0.ne')).const_mul
      (r ^ 2 / (r - 1))).sub
      ((hasDerivAt_rpow_const (p := r / 2) (Or.inl ht0.ne')).const_mul (4 * c))).add
      ((hasDerivAt_id t).const_mul (c ^ 2))) using 1
    rw [show r - 1 - 1 = (r / 2 - 1) * 2 by ring, Real.rpow_mul ht0.le, Real.rpow_two]
    field_simp
    ring
  have hc : c * (x - y) = 2 * (x ^ (r / 2) - y ^ (r / 2)) :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hyx.ne')
  dsimp [F] at h
  field_simp at h
  have h' := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hyx.le)
  calc
    _ = (r - 1) * (4 * (c * (x - y)) * (x ^ (r / 2) - y ^ (r / 2)) -
        (c * (x - y)) ^ 2) := by rw [hc]; ring
    _ ≤ _ := by linarith only [h']

private lemma power_gap {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 1 ≤ r) :
    4 * (r - 1) * (x ^ (r / 2) - y ^ (r / 2)) ^ 2 ≤
      r ^ 2 * (x - y) * (x ^ (r - 1) - y ^ (r - 1)) := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  rcases lt_trichotomy y x with h | rfl | h
  · exact power_gap_of_lt hy h hr
  · simp
  · linarith only [power_gap_of_lt hx h hr]

-- The entropy and power-difference estimates bound the change of exponent by the
-- dissipation under noise.
private lemma entropy_dissipation {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 1 ≤ r) :
    4 * (r - 1) * (r * (x ^ r * log x + y ^ r * log y) -
      (x ^ r + y ^ r) * log ((x ^ r + y ^ r) / 2)) ≤
      r ^ 2 * (x - y) * (x ^ (r - 1) - y ^ (r - 1)) := by
  have hs (z : ℝ) (hz : 0 < z) : (z ^ (r / 2)) ^ 2 = z ^ r := by
    rw [← Real.rpow_two, ← Real.rpow_mul hz.le]
    ring_nf
  have h := entropy_le (rpow_pos_of_pos hx (r / 2)) (rpow_pos_of_pos hy (r / 2))
  rw [hs x hx, hs y hy, log_rpow hx, log_rpow hy] at h
  apply le_trans _ (power_gap hx hy hr)
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  linarith only [h]

private noncomputable def pairNorm (r x y : ℝ) := ((x ^ r + y ^ r) / 2) ^ (1 / r)

private lemma pairNorm_mono {r p x y : ℝ} (hr : 0 < r) (hrp : r ≤ p)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : pairNorm r x y ≤ pairNorm p x y := by
  have hp := hr.trans_le hrp
  have hc := (convexOn_rpow (p := p / r) ((one_le_div hr).mpr hrp)).2
    (show x ^ r ∈ Ici 0 from rpow_nonneg hx r) (show y ^ r ∈ Ici 0 from rpow_nonneg hy r)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, ← rpow_mul hx, ← rpow_mul hy, show r * (p / r) = p by field_simp] at hc
  have hh : ((x ^ r + y ^ r) / 2) ^ (p / r) ≤ (x ^ p + y ^ p) / 2 := by
    convert hc using 2 <;> ring
  have hbase : 0 ≤ (x ^ r + y ^ r) / 2 := by positivity
  have h := rpow_le_rpow (rpow_nonneg hbase _) hh (by positivity : 0 ≤ 1 / p)
  rwa [← Real.rpow_mul hbase, show p / r * (1 / p) = 1 / r by field_simp] at h

private lemma pairNorm_self {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) : pairNorm r x x = x := by
  unfold pairNorm
  rw [show (x ^ r + x ^ r) / 2 = x ^ r by ring, ← rpow_mul hx]
  simp [hr.ne']

-- Along the curve r(t) = 1 + k/t² the two entries are m ± t*d.
private noncomputable def exponent (k t : ℝ) := 1 + k / t ^ 2

private lemma exponent_deriv {k t : ℝ} (ht : 0 < t) :
    HasDerivAt (exponent k) (-2 * (exponent k t - 1) / t) t := by
  convert! (((hasDerivAt_const t k).div (hasDerivAt_pow 2 t) (by positivity)).const_add 1) using 1
  dsimp [exponent]
  field_simp
  ring

private lemma path_deriv {m d k t : ℝ} (ht : 0 < t) (hk : 0 ≤ k)
    (hx : 0 < m + t * d) (hy : 0 < m - t * d) :
    ∃ D, HasDerivAt (fun s =>
      log (((m + s * d) ^ exponent k s + (m - s * d) ^ exponent k s) / 2) / exponent k s) D t
      ∧ 0 ≤ D := by
  let x := m + t * d
  let y := m - t * d
  let r := exponent k t
  let S := x ^ r + y ^ r
  have hr : 1 ≤ r := le_add_of_nonneg_right (div_nonneg hk (sq_nonneg t))
  have hr0 : 0 < r := one_pos.trans_le hr
  have hS : 0 < S := add_pos (rpow_pos_of_pos hx _) (rpow_pos_of_pos hy _)
  have hxy : x - y = 2 * t * d := by dsimp [x, y]; ring
  have he := exponent_deriv (k := k) ht
  have hlin := (hasDerivAt_id t).mul_const d
  have hA := ((hlin.const_add m).rpow he hx).add ((hlin.const_sub m).rpow he hy)
  have hL := ((hA.div_const 2).log (half_pos hS).ne').div he hr0.ne'
  refine ⟨_, hL, ?_⟩
  change 0 ≤ (((1 * d * r * x ^ (r - 1) + (-2 * (r - 1) / t) * x ^ r * log x +
    (-(1 * d) * r * y ^ (r - 1) + (-2 * (r - 1) / t) * y ^ r * log y)) / 2 /
    (S / 2)) * r - log (S / 2) * (-2 * (r - 1) / t)) / r ^ 2
  apply div_nonneg _ (sq_nonneg _)
  have h := entropy_dissipation hx hy hr
  rw [hxy] at h
  change 4 * (r - 1) * (r * (x ^ r * log x + y ^ r * log y) - S * log (S / 2)) ≤ _ at h
  field_simp
  linarith only [h]

private noncomputable def mix (t a b : ℝ) := (1 + t) / 2 * a + (1 - t) / 2 * b

private lemma mix_nonneg {t a b : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ mix t a b := by
  unfold mix
  exact add_nonneg (by positivity) (mul_nonneg (by linarith) hb)

private lemma mix_pos {t a b : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) : 0 < mix t a b := by
  unfold mix
  have ht' : 0 < (1 - t) / 2 := by linarith
  rcases lt_or_ge 0 a with h | h
  · positivity
  · have : 0 < b := by linarith
    positivity

private lemma two_point_bound {a b p q ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p)
    (hpq : p ≤ q) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hbound : (q - 1) * ρ ^ 2 ≤ p - 1) :
    pairNorm q (mix ρ a b) (mix ρ b a) ≤ pairNorm p a b := by
  have hq := hp.trans hpq
  have hq0 := one_pos.trans_le hq
  have hp0 := one_pos.trans_le hp
  obtain rfl | hρ := hρ.eq_or_lt
  · have h := pairNorm_mono (x := a) (y := b) one_pos hp ha hb
    simp only [mix, add_zero, sub_zero]
    rw [add_comm (1 / 2 * b), pairNorm_self (by positivity) hq0]
    simpa [pairNorm, add_div, div_eq_inv_mul, mul_add] using h
  by_cases hab : a + b = 0
  · obtain rfl : a = 0 := by linarith
    obtain rfl : b = 0 := by linarith
    simp [mix, pairNorm, zero_rpow hq0.ne', zero_rpow hp0.ne', hq0.ne', hp0.ne']
  have hab0 : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  -- The exponent at t = ρ is q. At t = 1 it is 1 + k ≤ p.
  let k := (q - 1) * ρ ^ 2
  let m := (a + b) / 2
  let d := (a - b) / 2
  have hk : 0 ≤ k := mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg _)
  have hx (t : ℝ) : m + t * d = mix t a b := by dsimp [m, d, mix]; ring
  have hy (t : ℝ) : m - t * d = mix t b a := by dsimp [m, d, mix]; ring
  have hr (t : ℝ) : 0 < exponent k t :=
    one_pos.trans_le (le_add_of_nonneg_right (div_nonneg hk (sq_nonneg t)))
  have heρ : exponent k ρ = q := by dsimp [exponent, k]; field_simp; ring
  have he1 : exponent k 1 = 1 + k := by simp [exponent]
  let S (t : ℝ) := ((m + t * d) ^ exponent k t + (m - t * d) ^ exponent k t) / 2
  have hS (t : ℝ) (ht : t ∈ Icc ρ 1) : 0 < S t := by
    have ht0 := hρ.trans_le ht.1
    have h1 := mix_nonneg ht0.le ht.2 ha hb
    have h2 := mix_nonneg ht0.le ht.2 hb ha
    rw [← hx] at h1
    rw [← hy] at h2
    have hm : 0 < m := half_pos hab0
    dsimp [S]
    rcases lt_or_ge 0 (m + t * d) with h | h
    · positivity
    · have : 0 < m - t * d := by linarith
      positivity
  have hpath := compare_endpoints (F := fun t => log (S t) / exponent k t) hρ1 (by
    intro t ht
    have ht0 := hρ.trans_le ht.1
    have hc := (exponent_deriv (k := k) ht0).continuousAt
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div _ hc (hr t).ne'
    apply ContinuousAt.log _ (hS t ht).ne'
    dsimp [S]
    apply ContinuousAt.div_const
    apply ContinuousAt.add <;> exact ContinuousAt.rpow (by fun_prop) hc (Or.inr (hr t))) <| by
      intro t ht
      have ht0 := hρ.trans ht.1
      apply path_deriv ht0 hk
      · rw [hx]; exact mix_pos ht0.le ht.2 ha hb hab0
      · rw [hy]; exact mix_pos ht0.le ht.2 hb ha (add_comm a b ▸ hab0)
  have hnorm (t : ℝ) (ht : t ∈ Icc ρ 1) :
      exp (log (S t) / exponent k t) = pairNorm (exponent k t) (mix t a b) (mix t b a) := by
    rw [pairNorm, ← hx, ← hy, rpow_def_of_pos (hS t ht)]
    congr 1
    ring
  have h := Real.exp_le_exp.mpr hpath
  rw [hnorm ρ (left_mem_Icc.mpr hρ1), hnorm 1 (right_mem_Icc.mpr hρ1), heρ, he1] at h
  have hmix (x y : ℝ) : mix 1 x y = x := by norm_num [mix]
  rw [hmix, hmix] at h
  exact h.trans (pairNorm_mono (by linarith) (by dsimp [k]; linarith) ha hb)

private lemma pairNorm_mono_entries {r a b c d : ℝ} (hr : 0 < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    pairNorm r a b ≤ pairNorm r c d := by
  unfold pairNorm
  apply rpow_le_rpow (by positivity) _ (by positivity)
  exact div_le_div_of_nonneg_right
    (add_le_add (rpow_le_rpow ha hac hr.le) (rpow_le_rpow hb hbd hr.le)) (by norm_num)

private lemma norm_split {n : ℕ} {r : ℝ} (hr : 0 < r) (f : BoolCube (n + 1) → ℝ) :
    bnt_qnorm r f = pairNorm r (bnt_qnorm r (fun ω => f (Fin.cons false ω)))
      (bnt_qnorm r (fun ω => f (Fin.cons true ω))) := by
  rw [pairNorm, bnt_qnorm_rpow_self hr.ne', bnt_qnorm_rpow_self hr.ne', bnt_qnorm,
    bnt_qnormPow_cons_split, Fintype.sum_bool, add_comm]

private lemma norm_mix_le {n : ℕ} {r ρ : ℝ} (hr : 1 ≤ r) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {u v : BoolCube n → ℝ} {a b : ℝ} (hu : bnt_qnorm r u ≤ a) (hv : bnt_qnorm r v ≤ b) :
    bnt_qnorm r (fun ω => mix ρ (u ω) (v ω)) ≤ mix ρ a b := by
  have hA : 0 ≤ (1 + ρ) / 2 := by positivity
  have hB : 0 ≤ (1 - ρ) / 2 := by linarith
  have hr0 := one_pos.trans_le hr
  unfold mix
  refine (bnt_qnorm_add_le hr _ _).trans ?_
  rw [bnt_qnorm_const_mul hr0, bnt_qnorm_const_mul hr0, abs_of_nonneg hA, abs_of_nonneg hB]
  exact add_le_add (mul_le_mul_of_nonneg_left hu hA) (mul_le_mul_of_nonneg_left hv hB)

private lemma tensorize {n : ℕ} (f : BoolCube n → ℝ) {p q ρ : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hbound : (q - 1) * ρ ^ 2 ≤ p - 1) :
    bnt_qnorm q (bnt_noiseOp ρ f) ≤ bnt_qnorm p f := by
  have hp0 := one_pos.trans_le hp
  have hq0 := hp0.trans_le hpq
  induction n with
  | zero => rw [bnt_noiseOp_fin_zero, bnt_qnorm_fin_zero hq0, bnt_qnorm_fin_zero hp0]
  | succ n ih =>
    let u (ω : BoolCube n) := f (Fin.cons false ω)
    let v (ω : BoolCube n) := f (Fin.cons true ω)
    have hfalse : (fun ω => bnt_noiseOp ρ f (Fin.cons false ω)) =
        fun ω => mix ρ (bnt_noiseOp ρ u ω) (bnt_noiseOp ρ v ω) := by
      funext ω
      exact bnt_noiseOp_cons_false ρ f ω
    have htrue : (fun ω => bnt_noiseOp ρ f (Fin.cons true ω)) =
        fun ω => mix ρ (bnt_noiseOp ρ v ω) (bnt_noiseOp ρ u ω) := by
      funext ω
      rw [bnt_noiseOp_cons_true, add_comm]
      rfl
    rw [norm_split hq0, norm_split hp0, hfalse, htrue]
    exact (pairNorm_mono_entries hq0 (bnt_qnorm_nonneg _ _) (bnt_qnorm_nonneg _ _)
      (norm_mix_le (hp.trans hpq) hρ hρ1 (ih u) (ih v))
      (norm_mix_le (hp.trans hpq) hρ hρ1 (ih v) (ih u))).trans
      (two_point_bound (bnt_qnorm_nonneg p u) (bnt_qnorm_nonneg p v) hp hpq hρ hρ1 hbound)

/-- **Hypercontractivity Theorem (Bonami–Beckner).** For `f : BoolCube n → ℝ`, real
`1 ≤ p ≤ q` and `0 ≤ ρ ≤ √((p - 1)/(q - 1))`, `‖T_ρ f‖_q ≤ ‖f‖_p`, where `T_ρ` is the noise
operator and `‖g‖_r = (𝔼|g|^r)^{1/r}` is `StatMech.Probability.bnt_qnorm r g` under the uniform
measure (A. Bonami, 1970; R. O'Donnell, *Analysis of Boolean Functions*, 2014, The
Hypercontractivity Theorem, Chapter 9 introduction, proved in Chapter 10). The case `q = ∞` of
the source is not covered. When `p = q = 1` Lean's `0 / 0 = 0` forces `ρ = 0`, a valid instance. -/
theorem hypercontractivity_theorem {n : ℕ} (f : BoolCube n → ℝ) {p q ρ : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
    bnt_qnorm q (boolNoiseOp ρ f) ≤ bnt_qnorm p f := by
  rw [← bnt_noiseOp_eq_boolNoiseOp]
  rcases (hp.trans hpq).eq_or_lt with hq | hq
  · subst q
    simp only [sub_self, div_zero, sqrt_zero] at hρ
    exact tensorize f hp hpq hρ0 (by linarith) (by nlinarith)
  · have hq' : 0 < q - 1 := sub_pos.mpr hq
    have hratio : (p - 1) / (q - 1) ≤ 1 := (div_le_one hq').mpr (by linarith)
    have hρ1 := hρ.trans (Real.sqrt_le_sqrt hratio)
    rw [Real.sqrt_one] at hρ1
    have hsq := sq_le_sq' (by linarith [sqrt_nonneg ((p - 1) / (q - 1))]) hρ
    rw [sq_sqrt (div_nonneg (sub_nonneg.mpr hp) hq'.le)] at hsq
    apply tensorize f hp hpq hρ0 hρ1
    linarith only [(le_div_iff₀ hq').mp hsq]

end BooleanCube
