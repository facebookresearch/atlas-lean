/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib

open scoped BigOperators
open Real Filter Topology Set Finset Asymptotics

set_option linter.style.longLine false

namespace StatMech
namespace OSSS.IntegrationSubcritical








theorem isc_gronwall_lower (a b lam : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
    Real.exp (lam * (b - a)) * f a ≤ f b := by
  set h : ℝ → ℝ := fun x => f x * Real.exp (-lam * x) with hh
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivAt h ((f' x - lam * f x) * Real.exp (-lam * x)) x := by
    intro x hx
    have hlin : HasDerivAt (fun y : ℝ => -lam * y) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    have h1 : HasDerivAt (fun y => Real.exp (-lam * y)) (Real.exp (-lam * x) * (-lam)) x :=
      (Real.hasDerivAt_exp (-lam * x)).comp x hlin
    have hp := (hd x hx).mul h1
    convert hp using 1; ring
  have hmono : MonotoneOn h (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x hx => (hderiv x (by simpa using hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x (mem_Icc_of_Ioo hx)).deriv]
      apply mul_nonneg
      · have := hineq x (mem_Icc_of_Ioo hx); linarith
      · exact (Real.exp_pos _).le
  have hle := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [hh] at hle; simp only [] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (lam * b)).le
  have e1 : Real.exp (-lam * a) * Real.exp (lam * b) = Real.exp (lam * (b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-lam * b) * Real.exp (lam * b) = 1 := by
    rw [← Real.exp_add, show -lam * b + lam * b = 0 by ring, Real.exp_zero]
  have lhs : f a * Real.exp (-lam * a) * Real.exp (lam * b)
      = Real.exp (lam * (b - a)) * f a := by rw [mul_assoc, e1]; ring
  have rhs : f b * Real.exp (-lam * b) * Real.exp (lam * b) = f b := by
    rw [mul_assoc, e2, mul_one]
  rw [lhs, rhs] at hmul; exact hmul



theorem isc_gronwall_decay (a b lam M : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x)
    (hfb : f b ≤ M) :
    f a ≤ M * Real.exp (-(lam * (b - a))) := by
  have hg := isc_gronwall_lower a b lam hab f f' hd hineq
  have hpos := Real.exp_pos (lam * (b - a))
  have h1 : Real.exp (lam * (b - a)) * f a ≤ M := hg.trans hfb
  rw [Real.exp_neg, le_mul_inv_iff₀ hpos]; linarith [h1]









theorem isc_summable_stretched_exp (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    Summable (fun n : ℕ => Real.exp (-(δ * (n : ℝ) ^ α))) := by
  have hlit : (fun x : ℝ => Real.exp (-(δ * x ^ α))) =o[atTop] (fun x : ℝ => x ^ (-(2 : ℝ))) := by
    have h := isLittleO_exp_neg_mul_rpow_atTop hδ (-2 / α)
    have hcomp := h.comp_tendsto (tendsto_rpow_atTop hα)
    refine hcomp.congr' ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with x _
      simp only [Function.comp_apply]; rw [neg_mul]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply]
      rw [← Real.rpow_mul hx.le]; congr 1; field_simp
  have hnat := hlit.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsumg : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    have := (Real.summable_one_div_nat_rpow (p := 2)).mpr (by norm_num)
    refine this.congr ?_; intro n; rw [Real.rpow_neg (by positivity), one_div]
  rw [← Nat.cofinite_eq_atTop] at hnat
  exact summable_of_isBigO hsumg hnat.isBigO










theorem isc_partial_sum_le (g b : ℕ → ℝ) (M : ℝ) (N n : ℕ)
    (hgM : ∀ k, g k ≤ M) (hMnn : 0 ≤ M)
    (hbnn : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hgb : ∀ k, N ≤ k → g k ≤ b k) :
    ∑ k ∈ Finset.range n, g k ≤ (N : ℝ) * M + ∑' k, b k := by
  rcases le_or_gt n N with hnN | hNn
  · have h1 : ∑ k ∈ Finset.range n, g k ≤ ∑ k ∈ Finset.range n, M :=
      Finset.sum_le_sum (fun k _ => hgM k)
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at h1
    have h2 : (n : ℝ) * M ≤ (N : ℝ) * M := by
      apply mul_le_mul_of_nonneg_right _ hMnn; exact_mod_cast hnN
    have htsum : 0 ≤ ∑' k, b k := tsum_nonneg hbnn
    linarith
  · rw [← Finset.sum_range_add_sum_Ico g (le_of_lt hNn)]
    have hpart1 : ∑ k ∈ Finset.range N, g k ≤ (N : ℝ) * M := by
      have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => hgM k)
      rw [Finset.sum_const, card_range, nsmul_eq_mul] at this; exact this
    have hpart2 : ∑ k ∈ Finset.Ico N n, g k ≤ ∑' k, b k :=
      calc ∑ k ∈ Finset.Ico N n, g k ≤ ∑ k ∈ Finset.Ico N n, b k :=
            Finset.sum_le_sum (fun k hk => hgb k (Finset.mem_Ico.mp hk).1)
        _ ≤ ∑' k, b k := hbsum.sum_le_tsum _ (fun k _ => hbnn k)
    linarith









theorem isc_rate_weaken (n : ℕ) (Sig fp fnx Q : ℝ) (hSig : 0 < Sig)
    (hSigle : Sig ≤ Q) (hfnn : 0 ≤ fnx)
    (hdi : ((n : ℝ) / Sig) * fnx ≤ fp) :
    ((n : ℝ) / Q) * fnx ≤ fp := by
  have h1 : (n : ℝ) / Q ≤ (n : ℝ) / Sig :=
    div_le_div_of_nonneg_left (by positivity) hSig hSigle
  calc ((n : ℝ) / Q) * fnx ≤ ((n : ℝ) / Sig) * fnx := mul_le_mul_of_nonneg_right h1 hfnn
    _ ≤ fp := hdi

end OSSS.IntegrationSubcritical
end StatMech
