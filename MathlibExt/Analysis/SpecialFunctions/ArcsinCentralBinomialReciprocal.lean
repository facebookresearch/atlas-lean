/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

namespace MetaMathlibExt

private noncomputable def Aterm (x : ℝ) (n : ℕ) : ℝ :=
  (2*x)^(2*n)/((n : ℝ)*(Nat.choose (2*n) n : ℝ))

private noncomputable def Sfun (x : ℝ) : ℝ := ∑' n, Aterm x n

private lemma choose_pos' (n : ℕ) : (0:ℝ) < (Nat.choose (2*n) n : ℝ) := by
  have h : 0 < Nat.choose (2*n) n := Nat.choose_pos (by omega)
  exact_mod_cast h

private lemma choose_ne' (n : ℕ) : (Nat.choose (2*n) n : ℝ) ≠ 0 :=
  ne_of_gt (choose_pos' n)

private lemma Aterm_zero (x : ℝ) : Aterm x 0 = 0 := by
  simp [Aterm]

private lemma choose_rec (n : ℕ) :
    (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)
      = (Nat.choose (2*n) n : ℝ)*(2*(2*(n:ℝ)+1)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n+1 ≤ 2*(n+1) by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
  have e1 : 2*(n+1) - (n+1) = n+1 := by omega
  have e2 : 2*n - n = n := by omega
  rw [e1] at h1; rw [e2] at h2
  have f1 : (((n+1).factorial:ℕ):ℝ) = ((n:ℝ)+1)*(((n.factorial):ℕ):ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : (((2*(n+1)).factorial : ℕ):ℝ) = (2*(n:ℝ)+2)*((((2*n+1).factorial) : ℕ):ℝ) := by
    have e : 2*(n+1) = (2*n+1)+1 := by omega
    rw [e, Nat.factorial_succ]; push_cast; ring
  have f3 : ((((2*n+1).factorial) : ℕ):ℝ) = (2*(n:ℝ)+1)*((((2*n).factorial):ℕ):ℝ) := by
    have e : 2*n+1 = (2*n)+1 := by omega
    rw [e, Nat.factorial_succ]; push_cast; ring
  have h1r : (Nat.choose (2*(n+1)) (n+1) : ℝ) * (((n:ℝ)+1) * ((n.factorial:ℕ):ℝ))
        * (((n:ℝ)+1) * ((n.factorial:ℕ):ℝ))
      = (2*(n:ℝ)+2) * ((2*(n:ℝ)+1) * ((Nat.choose (2*n) n : ℝ)
        * ((n.factorial:ℕ):ℝ) * ((n.factorial:ℕ):ℝ))) := by
    have h1r0 : (Nat.choose (2*(n+1)) (n+1) : ℝ) * (((n+1).factorial:ℕ):ℝ)
          * (((n+1).factorial:ℕ):ℝ) = (((2*(n+1)).factorial:ℕ):ℝ) := by
      exact_mod_cast h1
    have h2r0 : (Nat.choose (2*n) n : ℝ) * (((n.factorial):ℕ):ℝ) * (((n.factorial):ℕ):ℝ)
        = ((((2*n).factorial):ℕ):ℝ) := by exact_mod_cast h2
    rw [f1, f2, f3, ← h2r0] at h1r0
    linear_combination h1r0
  have hFn : (((n.factorial : ℕ)):ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hF2 : ((((n.factorial : ℕ)):ℝ))^2 ≠ 0 := pow_ne_zero 2 hFn
  have key : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)^2
      = (Nat.choose (2*n) n : ℝ) * (2*((n:ℝ)+1)*(2*(n:ℝ)+1)) := by
    have step : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)^2
          * ((((n.factorial : ℕ)):ℝ))^2
        = (Nat.choose (2*n) n : ℝ) * (2*((n:ℝ)+1)*(2*(n:ℝ)+1))
          * ((((n.factorial : ℕ)):ℝ))^2 := by
      linear_combination h1r
    exact mul_right_cancel₀ hF2 step
  have hNe : ((n:ℝ)+1) ≠ 0 := by positivity
  have hcancel : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1) * ((n:ℝ)+1)
      = ((Nat.choose (2*n) n : ℝ) * (2*(2*(n:ℝ)+1))) * ((n:ℝ)+1) := by
    linear_combination key
  exact mul_right_cancel₀ hNe hcancel

private lemma four_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (4^n : ℝ) ≤ 2*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hC21 : Nat.choose (2*1) 1 = 2 := by decide
    norm_num [hC21]
  | succ n hn ih =>
    have hr := choose_rec n
    have hC : (0:ℝ) ≤ (Nat.choose (2*n) n : ℝ) := le_of_lt (choose_pos' n)
    have e : (4^(n+1) : ℝ) = 4*4^n := by rw [pow_succ]; ring
    rw [e]
    push_cast
    calc (4:ℝ)*4^n ≤ 4*(2*(n:ℝ)*(Nat.choose (2*n) n : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by ring
      _ ≤ 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ) := by
          have h2 : ((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                - 4*(n:ℝ)*(Nat.choose (2*n) n : ℝ)
              = 2*(Nat.choose (2*n) n : ℝ) := by
            linear_combination hr
          have h3 : (0:ℝ) ≤ 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
              - 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
            have hexpand : 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                - 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ)
                = 2*((((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                  - 4*(n:ℝ)*(Nat.choose (2*n) n : ℝ))) := by ring
            rw [hexpand, h2]
            exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)
          linarith

private lemma ratio_le (n : ℕ) (hn : 1 ≤ n) :
    (4^n : ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)) ≤ 2 := by
  have hpos : (0:ℝ) < (n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
    apply mul_pos _ (choose_pos' n)
    exact_mod_cast (by omega : 0 < n)
  rw [div_le_iff₀ hpos]
  linear_combination (four_pow_le n hn)

private lemma summable_succ_mul_geom (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ((n:ℝ)+1)*q^n) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  have h2 := summable_geometric_of_lt_one hq0 hq1
  have e : (fun n : ℕ => ((n:ℝ)+1)*q^n)
      = (fun n : ℕ => ((n:ℝ)^1*q^n + q^n)) := by
    funext n; ring
  rw [e]
  exact h1.add h2

private lemma summable_Aterm (x : ℝ) (hx : |x| < 1) : Summable (Aterm x) := by
  have hx2 : x^2 < 1 := by
    nlinarith [hx, abs_nonneg x, sq_abs x]
  have hgeom := summable_geometric_of_lt_one (sq_nonneg x) hx2
  have hbound := (hgeom.mul_left 2)
  apply Summable.of_norm_bounded hbound
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [Aterm_zero]
    simp
  · have hC : (0:ℝ) < (Nat.choose (2*n) n : ℝ) := choose_pos' n
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hratio := ratio_le n (by omega)
    have hnorm : ‖Aterm x n‖ = ((4^n:ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)))*(x^2)^n := by
      simp only [Aterm, Real.norm_eq_abs, abs_div]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)*(Nat.choose (2*n) n : ℝ))]
      have habs : |(2*x)^(2*n)| = (4^n:ℝ)*(x^2)^n := by
        rw [abs_pow]
        have : |2*x|^(2*n) = (|2*x|^2)^n := by rw [← pow_mul]
        rw [this]
        have h2x : |2*x|^2 = 4*x^2 := by
          rw [sq_abs]; ring
        rw [h2x, mul_pow]
      rw [habs]
      ring
    rw [hnorm]
    calc ((4^n:ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)))*(x^2)^n
        ≤ 2*(x^2)^n := by
          apply mul_le_mul_of_nonneg_right hratio (pow_nonneg (sq_nonneg x) n)
      _ = 2*((x^2)^n) := by ring

private noncomputable def dcoef (n : ℕ) : ℝ := (4 ^ n : ℝ) / (Nat.choose (2 * n) n : ℝ)
private lemma dcoef_nonneg (n : ℕ) : 0 ≤ dcoef n := by
  unfold dcoef
  apply div_nonneg (pow_nonneg (by norm_num) n)
  exact le_of_lt (choose_pos' n)

private lemma dcoef_rec (n : ℕ) :
    (2 * (n : ℝ) + 1) * dcoef (n + 1) = 2 * ((n : ℝ) + 1) * dcoef n := by
  have hr := choose_rec n
  have hC0 : (Nat.choose (2 * n) n : ℝ) ≠ 0 := choose_ne' n
  have hC1 : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) ≠ 0 := choose_ne' (n + 1)
  have h4 : (4 ^ (n + 1) : ℝ) = 4 * 4 ^ n := by rw [pow_succ]; ring
  have e : (2 * (n : ℝ) + 1) * (4 * 4 ^ n) * (Nat.choose (2 * n) n : ℝ)
      = (2 * ((n : ℝ) + 1) * 4 ^ n) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) := by
    linear_combination (-2 * 4 ^ n) * hr
  simp only [dcoef, h4, ← mul_div_assoc]
  rw [div_eq_div_iff hC1 hC0]
  linear_combination e

private lemma dcoef_one : dcoef 1 = 2 := by
  have h : Nat.choose (2 * 1) 1 = 2 := by decide
  norm_num [dcoef, h]
private noncomputable def Dterm (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * x ^ (2 * n - 1)

private lemma Dterm_zero (x : ℝ) : Dterm x 0 = 0 := by simp [Dterm]

-- key bound for n ≥ 1
private lemma Dterm_bound (x : ℝ) (hx0 : x ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ‖Dterm x n‖ ≤ (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
  have hratio := ratio_le n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
  have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
    simp only [dcoef]; field_simp
  have hnorm : ‖Dterm x n‖ = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) * |x| ^ (2 * n - 1) := by
    simp only [Dterm, show n ≠ 0 by omega, ↓reduceIte]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [abs_of_nonneg (dcoef_nonneg n)]
    rw [abs_pow, hd]
  rw [hnorm]
  have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
  have hpow_abs : |x| ^ (2 * n - 1) = (|x| ^ 2) ^ n / |x| := by
    have h1 : |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [← pow_mul]
    have h2 : 2 * n = (2 * n - 1) + 1 := by omega
    have h3 : |x| ^ (2 * n) = |x| ^ (2 * n - 1) * |x| := by conv_lhs => rw [h2]; rw [pow_succ]
    have hne : |x| ≠ 0 := ne_of_gt habs
    have h4 : |x| ^ (2 * n - 1) = |x| ^ (2 * n) / |x| := by
      field_simp
      exact h3.symm
    rw [h4, h1]
  rw [hpow_abs]
  have hsq : (|x| ^ 2) ^ n = (x ^ 2) ^ n := by rw [sq_abs]
  rw [hsq]
  have hpos : (0:ℝ) ≤ (x ^ 2) ^ n / |x| := by positivity
  calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((x ^ 2) ^ n / |x|)
      ≤ (4 * (n : ℝ)) * ((x ^ 2) ^ n / |x|) := by
        have h4 : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ))
            ≤ 4 * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_right hle2 (le_of_lt hnR)
          linarith
        exact mul_le_mul_of_nonneg_right h4 hpos
    _ = (4 / |x|) * ((n : ℝ) * (x ^ 2) ^ n) := by ring
    _ ≤ (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (n : ℝ) * (x ^ 2) ^ n ≤ ((n : ℝ) + 1) * (x ^ 2) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sq_nonneg x) n)
        exact this

private lemma summable_Dterm (x : ℝ) (hx : |x| < 1) : Summable (Dterm x) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : Dterm 0 = fun _ => 0 := by
      funext n
      by_cases h : n = 0
      · simp [Dterm, h]
      · simp [Dterm, h, zero_pow (by omega : 2 * n - 1 ≠ 0)]
    rw [h0]; exact summable_zero
  · have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
    have hnn : 0 ≤ x ^ 2 := sq_nonneg x
    have hgeom := summable_succ_mul_geom (x ^ 2) hnn hx2
    have hC : Summable (fun n : ℕ => (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n)) :=
      hgeom.mul_left _
    apply Summable.of_norm_bounded hC
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [Dterm_zero, norm_zero]
      positivity
    · exact Dterm_bound x hx0 n (by omega)

private noncomputable def S2term (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * ((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 2)

private noncomputable def Dfun (x : ℝ) : ℝ := ∑' n, Dterm x n
private noncomputable def S2fun (x : ℝ) : ℝ := ∑' n, S2term x n
private noncomputable def Hfun (x : ℝ) : ℝ := (2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x

private lemma S2term_zero (x : ℝ) : S2term x 0 = 0 := by simp [S2term]

private lemma S2term_bound (x : ℝ) (hx0 : x ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ‖S2term x n‖ ≤ (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n)
      + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
  have hratio := ratio_le n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx2pos : (0:ℝ) < x ^ 2 := by positivity
  have hCnonneg : (0:ℝ) ≤ (4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) := by positivity
  have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
    have h : 1 ≤ 2 * n := by omega
    have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
    push_cast at hsub ⊢
    linarith
  have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
    simp only [dcoef]; field_simp
  have e1 : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
    positivity
  have e2 : (0:ℝ) ≤ 2 * (n : ℝ) - 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hnorm : ‖S2term x n‖
      = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ))
        * (2 * (n : ℝ) - 1) * |x| ^ (2 * n - 2) := by
    simp only [S2term, show n ≠ 0 by omega, ↓reduceIte, hcast, hd]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_pow, abs_of_nonneg e1, abs_of_nonneg e2]
  rw [hnorm]
  have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
  have hpow : |x| ^ (2 * n - 2) = (x ^ 2) ^ n / x ^ 2 := by
    have h1 : |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [← pow_mul]
    have h2 : 2 * n = (2 * n - 2) + 2 := by omega
    have h3 : |x| ^ (2 * n) = |x| ^ (2 * n - 2) * |x| ^ 2 := by
      conv_lhs => rw [h2]; rw [pow_add]
    have hne : (|x| ^ 2 : ℝ) ≠ 0 := by
      rw [sq_abs]; exact ne_of_gt hx2pos
    have hsq : (|x| ^ 2 : ℝ) = x ^ 2 := sq_abs x
    have h4 : |x| ^ (2 * n - 2) = |x| ^ (2 * n) / |x| ^ 2 := by
      field_simp; exact h3.symm
    rw [h4, h1, hsq]
  rw [hpow]
  have hpos : (0:ℝ) ≤ (x ^ 2) ^ n / x ^ 2 :=
    div_nonneg (pow_nonneg (sq_nonneg x) n) (sq_nonneg x)
  have hnn21 : (0:ℝ) ≤ (n : ℝ) * (2 * (n : ℝ) - 1) := by
    apply mul_nonneg (by positivity); linarith
  have hstep : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)
      ≤ 4 * ((n : ℝ) * (2 * (n : ℝ) - 1)) := by
    have hmul := mul_le_mul_of_nonneg_right hle2 hnn21
    linarith
  calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * ((x ^ 2) ^ n / x ^ 2)
      ≤ (4 * ((n : ℝ) * (2 * (n : ℝ) - 1))) * ((x ^ 2) ^ n / x ^ 2) :=
        mul_le_mul_of_nonneg_right hstep hpos
    _ = (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n) := by ring
    _ ≤ (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n) + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
        have hq : (0:ℝ) ≤ (x ^ 2) ^ n := pow_nonneg (sq_nonneg x) n
        have hcoef : (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1) := by
          nlinarith [sq_nonneg (n : ℝ)]
        have := mul_le_mul_of_nonneg_right hcoef hq
        have hdiv : (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n)
            ≤ (4 / x ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (x ^ 2) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [this]
        calc (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n)
            ≤ (4 / x ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (x ^ 2) ^ n) := hdiv
          _ = (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n) + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by ring

private lemma summable_S2term (x : ℝ) (hx : |x| < 1) : Summable (S2term x) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hsupp : Function.support (S2term 0) ⊆ {1} := by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      simp only [Set.mem_singleton_iff]
      by_contra hne
      apply hn
      simp only [S2term]
      split
      · rfl
      · rename_i h
        have : 2 ≤ n := by omega
        simp [zero_pow (by omega : 2 * n - 2 ≠ 0)]
    have hfin : Function.HasFiniteSupport (S2term 0) :=
      Set.Finite.subset (Set.finite_singleton 1) hsupp
    exact summable_of_hasFiniteSupport hfin
  · have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
    have hnn : 0 ≤ x ^ 2 := sq_nonneg x
    have hgeom1 := summable_succ_mul_geom (x ^ 2) hnn hx2
    have hnorm : ‖x ^ 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]; exact hx2
    have hgeom2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
    have hC : Summable (fun n : ℕ => (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n)
        + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n)) :=
      (hgeom2.mul_left _).add (hgeom1.mul_left _)
    apply Summable.of_norm_bounded hC
    intro n
    by_cases hn : n = 0
    · subst hn; simp only [S2term_zero, norm_zero]; positivity
    · exact S2term_bound x hx0 n (by omega)

private lemma two_pow_eq (n : ℕ) : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
  calc (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
    _ = 4 ^ n := by norm_num

private lemma hasDerivAt_Aterm (x : ℝ) (n : ℕ) : HasDerivAt (fun y => Aterm y n) (Dterm x n) x := by
  by_cases hn : n = 0
  · subst hn
    have hfun : (fun y => Aterm y 0) = fun _ => 0 := by
      funext y; simp [Aterm]
    rw [hfun, Dterm_zero]
    exact hasDerivAt_const x 0
  · have h2 : (2 : ℝ) ^ (2 * n) = 4 ^ n := two_pow_eq n
    have hfun : (fun y => Aterm y n)
        = fun y => ((2 ^ (2 * n) : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * y ^ (2 * n) := by
      funext y
      simp only [Aterm, mul_pow, h2]
      ring
    rw [hfun]
    have hderiv := (hasDerivAt_pow (2 * n) x).const_mul
      ((2 ^ (2 * n) : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)))
    have hcast : (((2 * n : ℕ)) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [hcast] at hderiv
    refine hderiv.congr_deriv ?_
    simp only [Dterm, hn, ↓reduceIte, dcoef, h2]
    field_simp

private lemma hasDerivAt_Dterm (x : ℝ) (n : ℕ) : HasDerivAt (fun y => Dterm y n) (S2term x n) x := by
  by_cases hn : n = 0
  · subst hn
    have hfun : (fun y => Dterm y 0) = fun _ => 0 := by
      funext y; simp [Dterm]
    rw [hfun, S2term_zero]
    exact hasDerivAt_const x 0
  · have hcast1 : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
      have h : 1 ≤ 2 * n := by omega
      have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
      push_cast at hsub ⊢
      linarith
    have hfun : (fun y => Dterm y n) = fun y => (2 * dcoef n) * y ^ (2 * n - 1) := by
      funext y; simp [Dterm, hn, mul_assoc]
    rw [hfun]
    have hderiv := (hasDerivAt_pow (2 * n - 1) x).const_mul (2 * dcoef n)
    have hexp : 2 * n - 1 - 1 = 2 * n - 2 := by omega
    rw [hexp, hcast1] at hderiv
    refine hderiv.congr_deriv ?_
    simp only [S2term, hn, ↓reduceIte, ← hcast1]
    ring

private lemma mem_ball_zero_iff (y r : ℝ) : y ∈ Metric.ball (0 : ℝ) r ↔ |y| < r := by
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]

private lemma Dterm_uniform_bound (r : ℝ) (hr : 0 < r) (n : ℕ) (y : ℝ)
    (hy : y ∈ Metric.ball (0 : ℝ) r) :
    ‖Dterm y n‖ ≤ (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
  have hyr : |y| < r := (mem_ball_zero_iff y r).mp hy
  have hyr0 : |y| ≤ r := le_of_lt hyr
  by_cases hn : n = 0
  · subst hn
    simp only [Dterm_zero, norm_zero]
    positivity
  · have hratio := ratio_le n (by omega)
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
      simp only [dcoef]; field_simp
    have epos : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
      positivity
    have hnorm : ‖Dterm y n‖
        = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) * |y| ^ (2 * n - 1) := by
      simp only [Dterm, hn, ↓reduceIte, hd]
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_pow, abs_of_nonneg epos]
    rw [hnorm]
    have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
    have hpow_le : |y| ^ (2 * n - 1) ≤ r ^ (2 * n - 1) :=
      pow_le_pow_left₀ (abs_nonneg y) hyr0 _
    have hpow_eq : r ^ (2 * n - 1) = (r ^ 2) ^ n / r := by
      have h1 : r ^ (2 * n) = (r ^ 2) ^ n := by rw [← pow_mul]
      have h2 : 2 * n = (2 * n - 1) + 1 := by omega
      have h3 : r ^ (2 * n) = r ^ (2 * n - 1) * r := by
        conv_lhs => rw [h2]; rw [pow_succ]
      have hne : (r : ℝ) ≠ 0 := ne_of_gt hr
      have h4 : r ^ (2 * n - 1) = r ^ (2 * n) / r := by
        field_simp; exact h3.symm
      rw [h4, h1]
    have hqpos : (0:ℝ) ≤ (r ^ 2) ^ n / r := by positivity
    have eA : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((r ^ 2) ^ n / r)
        ≤ 4 * ((n : ℝ) * ((r ^ 2) ^ n / r)) := by
      have hmul := mul_le_mul_of_nonneg_right hle2 (by positivity : (0:ℝ) ≤ (n : ℝ) * ((r ^ 2) ^ n / r))
      linarith
    have eB : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * |y| ^ (2 * n - 1)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (r ^ (2 * n - 1)) := by
      apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * |y| ^ (2 * n - 1)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (r ^ (2 * n - 1)) := eB
      _ = 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((r ^ 2) ^ n / r) := by
          rw [hpow_eq]
      _ ≤ 4 * ((n : ℝ) * ((r ^ 2) ^ n / r)) := eA
      _ = (4 / r) * ((n : ℝ) * (r ^ 2) ^ n) := by ring
      _ ≤ (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (n : ℝ) * (r ^ 2) ^ n ≤ ((n : ℝ) + 1) * (r ^ 2) ^ n :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sq_nonneg r) n)
          exact this

private lemma S2term_uniform_bound (r : ℝ) (hr : 0 < r) (n : ℕ) (y : ℝ)
    (hy : y ∈ Metric.ball (0 : ℝ) r) :
    ‖S2term y n‖ ≤ (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n)
      + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
  by_cases hn : n = 0
  · subst hn
    simp only [S2term_zero, norm_zero]
    positivity
  · have hyr0 : |y| ≤ r := le_of_lt ((mem_ball_zero_iff y r).mp hy)
    have hratio := ratio_le n (by omega)
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
      have h : 1 ≤ 2 * n := by omega
      have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
      push_cast at hsub ⊢
      linarith
    have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
      simp only [dcoef]; field_simp
    have e1 : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
      positivity
    have e2 : (0:ℝ) ≤ 2 * (n : ℝ) - 1 := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hnorm : ‖S2term y n‖
        = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ))
          * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2) := by
      simp only [S2term, hn, ↓reduceIte, hcast, hd]
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_pow, abs_of_nonneg e1, abs_of_nonneg e2]
    rw [hnorm]
    have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
    have hpow_le : |y| ^ (2 * n - 2) ≤ r ^ (2 * n - 2) :=
      pow_le_pow_left₀ (abs_nonneg y) hyr0 _
    have hpow_eq : r ^ (2 * n - 2) = (r ^ 2) ^ n / r ^ 2 := by
      have h1 : r ^ (2 * n) = (r ^ 2) ^ n := by rw [← pow_mul]
      have h2 : 2 * n = (2 * n - 2) + 2 := by omega
      have h3 : r ^ (2 * n) = r ^ (2 * n - 2) * r ^ 2 := by
        conv_lhs => rw [h2]; rw [pow_add]
      have hne : (r ^ 2 : ℝ) ≠ 0 := by positivity
      have h4 : r ^ (2 * n - 2) = r ^ (2 * n) / r ^ 2 := by
        field_simp; exact h3.symm
      rw [h4, h1]
    have hnn21 : (0:ℝ) ≤ (n : ℝ) * (2 * (n : ℝ) - 1) := by
      apply mul_nonneg (by positivity); linarith
    have hstep : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)
        ≤ 4 * ((n : ℝ) * (2 * (n : ℝ) - 1)) := by
      have hmul := mul_le_mul_of_nonneg_right hle2 hnn21
      linarith
    have hmono : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * r ^ (2 * n - 2) := by
      apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * r ^ (2 * n - 2) := hmono
      _ = (2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)) * (r ^ (2 * n - 2)) := by ring
      _ = (2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)) * ((r ^ 2) ^ n / r ^ 2) := by
          rw [hpow_eq]
      _ ≤ (4 * ((n : ℝ) * (2 * (n : ℝ) - 1))) * ((r ^ 2) ^ n / r ^ 2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n) := by ring
      _ ≤ (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
          have hq : (0:ℝ) ≤ (r ^ 2) ^ n := pow_nonneg (sq_nonneg r) n
          have hcoef : (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1) := by
            nlinarith [sq_nonneg (n : ℝ)]
          have hmul2 := mul_le_mul_of_nonneg_right hcoef hq
          have hdiv : (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n)
              ≤ (4 / r ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (r ^ 2) ^ n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hmul2]
          calc (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n)
              ≤ (4 / r ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (r ^ 2) ^ n) := hdiv
            _ = (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by ring

private lemma hasDerivAt_Sfun (x : ℝ) (hx : |x| < 1) : HasDerivAt Sfun (Dfun x) x := by
  set r := (|x| + 1) / 2 with hr_def
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hrr : r < 1 := by
    have : |x| < 1 := hx
    linarith
  have hxr : |x| < r := by linarith [hx]
  have hr2 : r ^ 2 < 1 := by nlinarith [hr0, hrr, sq_nonneg r]
  have hr2nn : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
  set s := Metric.ball (0 : ℝ) r with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hxs : x ∈ s := (mem_ball_zero_iff x r).mpr hxr
  have hgeom := summable_succ_mul_geom (r ^ 2) hr2nn hr2
  have hu : Summable (fun n : ℕ => (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n)) :=
    hgeom.mul_left _
  have hunif : TendstoUniformlyOn (fun N y => ∑ n ∈ Finset.range N, Dterm y n)
      (fun y => ∑' n, Dterm y n) Filter.atTop s :=
    tendstoUniformlyOn_tsum_nat hu (fun n y hy => Dterm_uniform_bound r hr0 n y hy)
  have hderiv_each : ∀ᶠ N in Filter.atTop,
      ∀ y ∈ s, HasDerivAt (fun y => ∑ n ∈ Finset.range N, Aterm y n)
        (∑ n ∈ Finset.range N, Dterm y n) y := by
    apply Filter.Eventually.of_forall
    intro N y _
    have h := HasDerivAt.sum (u := Finset.range N)
      (A := fun n y => Aterm y n) (A' := fun n => Dterm y n)
      (fun i _ => hasDerivAt_Aterm y i)
    have hfun : (∑ i ∈ Finset.range N, fun y => Aterm y i)
        = (fun y => ∑ n ∈ Finset.range N, Aterm y n) := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hlim : ∀ y ∈ s, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, Aterm y n)
      Filter.atTop (nhds (Sfun y)) := by
    intro y hy
    have hy1 : |y| < 1 := lt_trans ((mem_ball_zero_iff y r).mp hy) hrr
    have hsum := (summable_Aterm y hy1).hasSum
    have htend := hsum.tendsto_sum_nat
    simpa [Sfun] using htend
  have hmain := hasDerivAt_of_tendstoUniformlyOn hs_open hunif hderiv_each hlim hxs
  simpa [Sfun, Dfun] using hmain

private lemma hasDerivAt_Dfun (x : ℝ) (hx : |x| < 1) : HasDerivAt Dfun (S2fun x) x := by
  set r := (|x| + 1) / 2 with hr_def
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hrr : r < 1 := by linarith [hx]
  have hxr : |x| < r := by linarith [hx]
  have hr2 : r ^ 2 < 1 := by nlinarith [hr0, hrr, sq_nonneg r]
  have hr2nn : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
  set s := Metric.ball (0 : ℝ) r with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hxs : x ∈ s := (mem_ball_zero_iff x r).mpr hxr
  have hnorm : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2nn]; exact hr2
  have hgeom1 := summable_succ_mul_geom (r ^ 2) hr2nn hr2
  have hgeom2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
  have hu : Summable (fun n : ℕ => (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n)
      + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n)) :=
    (hgeom2.mul_left _).add (hgeom1.mul_left _)
  have hunif : TendstoUniformlyOn (fun N y => ∑ n ∈ Finset.range N, S2term y n)
      (fun y => ∑' n, S2term y n) Filter.atTop s :=
    tendstoUniformlyOn_tsum_nat hu (fun n y hy => S2term_uniform_bound r hr0 n y hy)
  have hderiv_each : ∀ᶠ N in Filter.atTop,
      ∀ y ∈ s, HasDerivAt (fun y => ∑ n ∈ Finset.range N, Dterm y n)
        (∑ n ∈ Finset.range N, S2term y n) y := by
    apply Filter.Eventually.of_forall
    intro N y _
    have h := HasDerivAt.sum (u := Finset.range N)
      (A := fun n y => Dterm y n) (A' := fun n => S2term y n)
      (fun i _ => hasDerivAt_Dterm y i)
    have hfun : (∑ i ∈ Finset.range N, fun y => Dterm y i)
        = (fun y => ∑ n ∈ Finset.range N, Dterm y n) := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hlim : ∀ y ∈ s, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, Dterm y n)
      Filter.atTop (nhds (Dfun y)) := by
    intro y hy
    have hy1 : |y| < 1 := lt_trans ((mem_ball_zero_iff y r).mp hy) hrr
    have hsum := (summable_Dterm y hy1).hasSum
    have htend := hsum.tendsto_sum_nat
    simpa [Dfun] using htend
  have hmain := hasDerivAt_of_tendstoUniformlyOn hs_open hunif hderiv_each hlim hxs
  simpa [Dfun, S2fun] using hmain

private lemma S2term_one (x : ℝ) : S2term x 1 = 4 := by
  have h1 : S2term x 1 = 2 * dcoef 1 * ((2 * 1 - 1 : ℕ) : ℝ) * x ^ (2 * 1 - 2) := by
    simp [S2term]
  rw [h1]
  norm_num [dcoef_one]

private lemma S2term_succ (x : ℝ) (m : ℕ) :
    S2term x (m + 1) = 2 * dcoef (m + 1) * (2 * (m : ℝ) + 1) * x ^ (2 * m) := by
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have hcast : (((2 * (m + 1) - 1 : ℕ)) : ℝ) = 2 * (m : ℝ) + 1 := by
    rw [h1]; push_cast; ring
  simp only [S2term, show m + 1 ≠ 0 by omega, ↓reduceIte, hcast, h2]

private lemma Dterm_succ (x : ℝ) (m : ℕ) :
    Dterm x (m + 1) = 2 * dcoef (m + 1) * x ^ (2 * m + 1) := by
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  simp only [Dterm, show m + 1 ≠ 0 by omega, ↓reduceIte, h1]

private lemma ode_S (x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * S2fun x - 3 * x * Dfun x = 4 := by
  have hS2 := summable_S2term x hx
  have hD := summable_Dterm x hx
  have hS2s : Summable (fun m => S2term x (m + 1)) :=
    (summable_nat_add_iff (f := S2term x) 1).mpr hS2
  have hDs : Summable (fun m => Dterm x (m + 1)) :=
    (summable_nat_add_iff (f := Dterm x) 1).mpr hD
  have hS2ss : Summable (fun m => S2term x (m + 1 + 1)) :=
    (summable_nat_add_iff (f := fun m => S2term x (m + 1)) 1).mpr hS2s
  have hshift : ∑' n, S2term x n = ∑' m, S2term x (m + 1) := by
    have h := hS2.tsum_eq_zero_add
    rw [S2term_zero, zero_add] at h
    exact h
  have hpeel : (∑' m, S2term x (m + 1)) = S2term x 1 + ∑' m, S2term x (m + 1 + 1) := by
    simpa using hS2s.tsum_eq_zero_add
  have hDshift : ∑' n, Dterm x n = ∑' m, Dterm x (m + 1) := by
    have h := hD.tsum_eq_zero_add
    rw [Dterm_zero, zero_add] at h
    exact h
  have hB : Summable (fun m => x ^ 2 * S2term x (m + 1)) := hS2s.mul_left _
  have hC : Summable (fun m => (3 * x) * Dterm x (m + 1)) := hDs.mul_left _
  have hBtsum : (∑' m, x ^ 2 * S2term x (m + 1)) = x ^ 2 * (∑' m, S2term x (m + 1)) :=
    hS2s.tsum_mul_left _
  have hCtsum : (∑' m, (3 * x) * Dterm x (m + 1)) = (3 * x) * (∑' m, Dterm x (m + 1)) :=
    hDs.tsum_mul_left _
  have hzero : (fun m => S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)) = fun _ => 0 := by
    funext m
    have e1 := S2term_succ x (m + 1)
    have e2 := S2term_succ x m
    have e3 := Dterm_succ x m
    have hrec := dcoef_rec (m + 1)
    have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hrec
    rw [e1, e2, e3, hcast]
    have pA : x ^ (2 * (m + 1)) = x ^ 2 * x ^ (2 * m) := by
      rw [← pow_add]
      congr 1
      omega
    have pB : x ^ (2 * m + 1) = x ^ (2 * m) * x := by
      rw [← pow_succ]
    rw [pA, pB]
    linear_combination 2 * (x ^ 2 * x ^ (2 * m)) * hrec
  have hsum0 : ∑' m, (S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)) = 0 := by
    rw [hzero]
    exact tsum_zero
  have hAB : Summable (fun m => S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)) :=
    hS2ss.sub hB
  have hdecomp : (∑' m, (S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)))
      = (∑' m, S2term x (m + 1 + 1)) - (∑' m, x ^ 2 * S2term x (m + 1))
        - (∑' m, (3 * x) * Dterm x (m + 1)) := by
    rw [Summable.tsum_sub hAB hC, Summable.tsum_sub hS2ss hB]
  have hpeel4 : (∑' m, S2term x (m + 1)) = 4 + ∑' m, S2term x (m + 1 + 1) := by
    rw [hpeel, S2term_one]
  have hzz : (∑' m, S2term x (m + 1 + 1)) - (∑' m, x ^ 2 * S2term x (m + 1))
      - (∑' m, (3 * x) * Dterm x (m + 1)) = 0 := hdecomp.symm.trans hsum0
  have key : (1 - x ^ 2) * (∑' n, S2term x n) - 3 * x * (∑' n, Dterm x n) = 4 := by
    linear_combination (1 - x ^ 2) * hshift - (3 * x) * hDshift + hpeel4 + hzz + hBtsum + hCtsum
  show (1 - x ^ 2) * S2fun x - 3 * x * Dfun x = 4
  exact key

private lemma hpos_of_mem (x : ℝ) (hx : |x| < 1) : (0:ℝ) < 1 - x ^ 2 := by
  have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
  linarith

private lemma hne_one_of_mem (x : ℝ) (hx : |x| < 1) : x ≠ 1 ∧ x ≠ -1 := by
  constructor
  · intro h; rw [h] at hx; norm_num at hx
  · intro h; rw [h] at hx; norm_num at hx

private noncomputable def H1fun (x : ℝ) : ℝ :=
  2 * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 3 + 2 * x / (1 - x ^ 2)

private lemma hasDerivAt_H (x : ℝ) (hx : |x| < 1) : HasDerivAt Hfun (H1fun x) x := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  obtain ⟨hne1, hnem1⟩ := hne_one_of_mem x hx
  have h_inner : HasDerivAt (fun y => (1:ℝ) - y ^ 2) (-2 * x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
    have h3 := h2.sub h1
    refine h3.congr_deriv ?_
    ring
  have h_sqrt : HasDerivAt (fun y => Real.sqrt (1 - y ^ 2)) ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    h_inner.sqrt hne
  have h_2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have h_div := h_2x.div h_sqrt hne_sqrt
  have h_arcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
    have h := Real.hasDerivAt_arcsin hnem1 hne1
    simpa using h
  have hH : HasDerivAt (fun y => (2 * y / Real.sqrt (1 - y ^ 2)) * Real.arcsin y)
      ((2 * Real.sqrt (1 - x ^ 2) - 2 * x * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2))))
        / (Real.sqrt (1 - x ^ 2)) ^ 2 * Real.arcsin x
        + (2 * x / Real.sqrt (1 - x ^ 2)) * (1 / Real.sqrt (1 - x ^ 2))) x :=
    h_div.mul h_arcsin
  have hHfun : (fun y => (2 * y / Real.sqrt (1 - y ^ 2)) * Real.arcsin y) = Hfun := by
    funext y
    simp [Hfun, mul_div_assoc]
  rw [hHfun] at hH
  refine hH.congr_deriv ?_
  simp only [H1fun]
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  field_simp
  linear_combination (-x * Real.sqrt (1 - x ^ 2) + Real.arcsin x * (1 - x ^ 2)) * hsq

private noncomputable def H2fun (x : ℝ) : ℝ :=
  6 * x * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 5 + (4 + 2 * x ^ 2) / (1 - x ^ 2) ^ 2

private lemma hasDerivAt_H1 (x : ℝ) (hx : |x| < 1) : HasDerivAt H1fun (H2fun x) x := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  obtain ⟨hne1, hnem1⟩ := hne_one_of_mem x hx
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  -- inner sqrt derivative
  have h_inner : HasDerivAt (fun y => (1:ℝ) - y ^ 2) (-2 * x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
    have h3 := h2.sub h1
    refine h3.congr_deriv ?_
    ring
  have h_sqrt : HasDerivAt (fun y => Real.sqrt (1 - y ^ 2)) ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    h_inner.sqrt hne
  have h_arcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
    have h := Real.hasDerivAt_arcsin hnem1 hne1
    simpa using h
  -- numerator 2*arcsin
  have h_num : HasDerivAt (fun y => 2 * Real.arcsin y) (2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
    have h := h_arcsin.const_mul 2
    simpa [mul_assoc] using h
  -- denominator s^3
  have h_den : HasDerivAt (fun y => (Real.sqrt (1 - y ^ 2)) ^ 3)
      (3 * (Real.sqrt (1 - x ^ 2)) ^ 2 * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2)))) x :=
    h_sqrt.pow 3
  have hne3 : (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := pow_ne_zero 3 hne_sqrt
  have h_term1 := h_num.div h_den hne3
  -- second term 2x/(1-x^2)
  have h_2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have h_u : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := h_inner
  have h_term2 := h_2x.div h_u hne
  have hH1 : HasDerivAt H1fun
      ((2 * (1 / Real.sqrt (1 - x ^ 2)) * (Real.sqrt (1 - x ^ 2)) ^ 3
        - 2 * Real.arcsin x * (3 * (Real.sqrt (1 - x ^ 2)) ^ 2 * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2)))))
        / ((Real.sqrt (1 - x ^ 2)) ^ 3) ^ 2
      + (2 * (1 - x ^ 2) - 2 * x * (-2 * x)) / (1 - x ^ 2) ^ 2) x :=
    h_term1.add h_term2
  refine hH1.congr_deriv ?_
  simp only [H2fun]
  field_simp
  linear_combination (-2 * Real.sqrt (1 - x ^ 2) * ((1 - x ^ 2) + (Real.sqrt (1 - x ^ 2)) ^ 2)) * hsq

private lemma ode_H (x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * H2fun x - 3 * x * H1fun x = 4 := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  simp only [H1fun, H2fun]
  have hs3 : (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := pow_ne_zero 3 hne_sqrt
  have hs5 : (Real.sqrt (1 - x ^ 2)) ^ 5 ≠ 0 := pow_ne_zero 5 hne_sqrt
  have hsq2 : ((1:ℝ) - x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  field_simp [hs3, hs5, hsq2, hne, hne_sqrt]
  linear_combination (-6 * x * Real.arcsin x * (1 - x ^ 2)) * hsq

private lemma Sfun_zero : Sfun 0 = 0 := by
  have h0 : Aterm 0 = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [Aterm, hn]
    · have h2n : 2 * n ≠ 0 := by omega
      simp [Aterm, zero_pow h2n]
  simp only [Sfun]
  rw [h0]
  exact tsum_zero

private lemma Dfun_zero : Dfun 0 = 0 := by
  have h0 : Dterm 0 = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [Dterm, hn]
    · simp [Dterm, hn, zero_pow (by omega : 2 * n - 1 ≠ 0)]
  simp only [Dfun]
  rw [h0]
  exact tsum_zero

private lemma Hfun_zero : Hfun 0 = 0 := by simp [Hfun, Real.arcsin_zero]

private lemma H1fun_zero : H1fun 0 = 0 := by simp [H1fun, Real.arcsin_zero]

-- difference of derivatives satisfies homogeneous ODE
private lemma hodeK (y : ℝ) (hy : |y| < 1) :
    (1 - y ^ 2) * (S2fun y - H2fun y) - 3 * y * (Dfun y - H1fun y) = 0 := by
  have h1 := ode_S y hy
  have h2 := ode_H y hy
  linear_combination h1 - h2

private noncomputable def Jfun (y : ℝ) : ℝ :=
  (Dfun y - H1fun y) * (Real.sqrt (1 - y ^ 2)) ^ 3

private lemma hasDerivAt_Jfun (y : ℝ) (hy : |y| < 1) : HasDerivAt Jfun 0 y := by
  have hpos : (0:ℝ) < 1 - y ^ 2 := hpos_of_mem y hy
  have hne : (1:ℝ) - y ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - y ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have hK : HasDerivAt (fun z => Dfun z - H1fun z) (S2fun y - H2fun y) y :=
    (hasDerivAt_Dfun y hy).sub (hasDerivAt_H1 y hy)
  have h_inner : HasDerivAt (fun z => (1:ℝ) - z ^ 2) (-2 * y) y := by
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
      have h := hasDerivAt_pow 2 y
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 y := hasDerivAt_const y 1
    have h3 := h2.sub h1
    refine h3.congr_deriv ?_
    ring
  have h_sqrt : HasDerivAt (fun z => Real.sqrt (1 - z ^ 2)) ((-2 * y) / (2 * Real.sqrt (1 - y ^ 2))) y :=
    h_inner.sqrt hne
  have h_pow : HasDerivAt (fun z => (Real.sqrt (1 - z ^ 2)) ^ 3)
      (3 * (Real.sqrt (1 - y ^ 2)) ^ 2 * (((-2 * y) / (2 * Real.sqrt (1 - y ^ 2))))) y :=
    h_sqrt.pow 3
  have hJ : HasDerivAt Jfun
      ((S2fun y - H2fun y) * (Real.sqrt (1 - y ^ 2)) ^ 3
        + (Dfun y - H1fun y) * (3 * (Real.sqrt (1 - y ^ 2)) ^ 2 * (((-2 * y) / (2 * Real.sqrt (1 - y ^ 2)))))) y :=
    hK.mul h_pow
  refine hJ.congr_deriv ?_
  have hK0 := hodeK y hy
  field_simp
  linear_combination (Real.sqrt (1 - y ^ 2)) * hK0
    + (S2fun y - H2fun y) * (Real.sqrt (1 - y ^ 2)) * hsq

private lemma K_eq_zero (y : ℝ) (hy : |y| < 1) : Dfun y - H1fun y = 0 := by
  set s := Metric.ball (0 : ℝ) 1 with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hs_conn : IsPreconnected s := (convex_ball (0 : ℝ) 1).isPreconnected
  have hmem : ∀ z ∈ s, |z| < 1 := fun z hz => (mem_ball_zero_iff z 1).mp hz
  have hdiff : DifferentiableOn ℝ Jfun s := by
    intro z hz
    exact ((hasDerivAt_Jfun z (hmem z hz)).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv Jfun) 0 s := by
    intro z hz
    have h := (hasDerivAt_Jfun z (hmem z hz)).deriv
    simp [h]
  have hJ0 : Jfun 0 = 0 := by simp [Jfun, Dfun_zero, H1fun_zero]
  have h0mem : (0:ℝ) ∈ s := (mem_ball_zero_iff 0 1).mpr (by norm_num)
  have hymem : y ∈ s := (mem_ball_zero_iff y 1).mpr hy
  have hJy : Jfun y = Jfun 0 := hs_open.is_const_of_deriv_eq_zero hs_conn hdiff hderiv hymem h0mem
  rw [hJ0] at hJy
  have hpos : (0:ℝ) < 1 - y ^ 2 := hpos_of_mem y hy
  have hne3 : (Real.sqrt (1 - y ^ 2)) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (Real.sqrt_ne_zero'.mpr hpos)
  simp only [Jfun] at hJy
  exact (mul_eq_zero.mp hJy).resolve_right hne3

private lemma SH_eq (y : ℝ) (hy : |y| < 1) : Sfun y = Hfun y := by
  set s := Metric.ball (0 : ℝ) 1 with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hs_conn : IsPreconnected s := (convex_ball (0 : ℝ) 1).isPreconnected
  have hmem : ∀ z ∈ s, |z| < 1 := fun z hz => (mem_ball_zero_iff z 1).mp hz
  have hL : ∀ z ∈ s, HasDerivAt (fun w => Sfun w - Hfun w) 0 z := by
    intro z hz
    have hz1 := hmem z hz
    have h := (hasDerivAt_Sfun z hz1).sub (hasDerivAt_H z hz1)
    have hK := K_eq_zero z hz1
    refine h.congr_deriv ?_
    linarith [hK]
  have hdiff : DifferentiableOn ℝ (fun w => Sfun w - Hfun w) s := by
    intro z hz
    exact ((hL z hz).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun w => Sfun w - Hfun w)) 0 s := by
    intro z hz
    have h := (hL z hz).deriv
    simp [h]
  have h0mem : (0:ℝ) ∈ s := (mem_ball_zero_iff 0 1).mpr (by norm_num)
  have hymem : y ∈ s := (mem_ball_zero_iff y 1).mpr hy
  have hLy : (Sfun y - Hfun y) = (Sfun 0 - Hfun 0) :=
    hs_open.is_const_of_deriv_eq_zero hs_conn hdiff hderiv hymem h0mem
  rw [Sfun_zero, Hfun_zero] at hLy
  linarith [hLy]

/--
**Lehmer's central binomial series for arcsin.** For every real number $x$ with $|x| < 1$, the
series
$$\sum_{m=1}^{\infty} \frac{(2x)^{2m}}{m \binom{2m}{m}}$$
converges unconditionally, and its sum is $\dfrac{2x}{\sqrt{1 - x^2}} \arcsin x$.

The source attributes the identity to D. H. Lehmer.

Proves `Wanted` entry `arcsin_central_binomial_reciprocal_series`.

Source: B. Sury, Tianming Wang, and Feng-Zhen Zhao, "Identities
Involving Reciprocals of Binomial Coefficients," Journal of Integer
Sequences 7 (2004), Article 04.2.8, Theorem, lines 365–371,
https://cs.uwaterloo.ca/journals/JIS/VOL7/Sury/sury99.tex
-/
theorem arcsin_central_binomial_reciprocal_series
    (x : ℝ)
    (hx : |x| < 1) :
    HasSum (fun m : ℕ =>
        (2 * x) ^ (2 * (m + 1)) / ((↑(m + 1) : ℝ) * ↑(Nat.choose (2 * (m + 1)) (m + 1))))
      ((2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x) := by
  have hSH : Sfun x = Hfun x := SH_eq x hx
  have hsum := (summable_Aterm x hx).hasSum
  have hsumH : HasSum (Aterm x) (Hfun x) := hSH ▸ hsum
  have hbase : HasSum (Aterm x) (Hfun x + ∑ i ∈ Finset.range 1, Aterm x i) := by
    rw [Finset.sum_range_one, Aterm_zero, add_zero]
    exact hsumH
  have hshifted : HasSum (fun m => Aterm x (m + 1)) (Hfun x) :=
    (hasSum_nat_add_iff 1).mpr hbase
  show HasSum (fun m => Aterm x (m + 1)) (Hfun x)
  exact hshifted

end MetaMathlibExt
