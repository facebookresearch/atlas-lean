/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Set

namespace StatMech.Ising

noncomputable section



theorem hasDerivAt_tanh (x : Real) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  rw [show Real.tanh = fun y : Real => Real.sinh y / Real.cosh y by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  convert h using 1
  rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]]


theorem antitoneOn_tanh_div :
    AntitoneOn (fun x : Real => Real.tanh x / x) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : Real))
  · have htanh : Continuous Real.tanh := by
      rw [show Real.tanh = Real.sinh / Real.cosh by
        funext y
        exact Real.tanh_eq_sinh_div_cosh y]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun y => (Real.cosh_pos y).ne')
    exact htanh.continuousOn.div continuous_id.continuousOn
      (fun x hx => (ne_of_gt hx))
  · intro x hx
    rw [interior_Ioi] at hx
    simpa only [Pi.div_apply, id_eq] using
      ((hasDerivAt_tanh x).div (hasDerivAt_id x)
        (ne_of_gt hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hsinh : 2 * x <= Real.sinh (2 * x) :=
      Real.self_le_sinh_iff.mpr (by positivity)
    rw [Real.sinh_two_mul] at hsinh
    have hderiv := ((hasDerivAt_tanh x).div (hasDerivAt_id x) hx0.ne').deriv
    change deriv (Real.tanh / id) x <= 0
    rw [hderiv]
    have hcosh : 0 < Real.cosh x := Real.cosh_pos x
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
    have hxc : x <= Real.sinh x * Real.cosh x := by nlinarith
    apply (div_nonpos_iff).2
    right
    constructor
    · apply sub_nonpos.mpr
      rw [Real.tanh_eq_sinh_div_cosh]
      simp only [id_eq, mul_one]
      rw [show 1 / Real.cosh x ^ 2 * x = x / Real.cosh x ^ 2 by ring]
      rw [div_le_div_iff₀ (sq_pos_of_pos hcosh) hcosh]
      nlinarith [sq_pos_of_pos hcosh]
    · exact sq_nonneg x



theorem mul_tanh_le_tanh_mul
    {a x : Real} (ha0 : 0 <= a) (ha1 : a <= 1) (hx : 0 <= x) :
    a * Real.tanh x <= Real.tanh (a * x) := by
  rcases eq_or_lt_of_le ha0 with rfl | ha
  · simp
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  have hax : 0 < a * x := mul_pos ha hx
  have hle : a * x <= x := by nlinarith
  have hratio := antitoneOn_tanh_div hax hx hle
  have hxne : x ≠ 0 := hx.ne'
  have haxne : a * x ≠ 0 := hax.ne'
  rw [div_le_div_iff₀ hx hax] at hratio
  field_simp [hxne, haxne] at hratio ⊢
  nlinarith



theorem artanh_mul_tanh_le_mul
    {a x : Real} (ha0 : 0 <= a) (ha1 : a <= 1) (hx : 0 <= x) :
    Real.artanh (a * Real.tanh x) <= a * x := by
  have ht0 : 0 <= Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le
  have ht1 : Real.tanh x < 1 := Real.tanh_lt_one x
  have hat0 : 0 <= a * Real.tanh x := mul_nonneg ha0 ht0
  have hat1 : a * Real.tanh x < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left ht0 ha1) ht1
  have hscaled := mul_tanh_le_tanh_mul ha0 ha1 hx
  calc
    Real.artanh (a * Real.tanh x) <= Real.artanh (Real.tanh (a * x)) :=
      Real.artanh_le_artanh (by linarith) (Real.tanh_lt_one _) hscaled
    _ = a * x := Real.artanh_tanh _


def singleBondInterfaceFreeEnergy (K m1 m2 : Real) : Real :=
  Real.log ((1 + m1 * m2 * Real.tanh K) /
    (1 - m1 * m2 * Real.tanh K))




theorem singleBondInterfaceFreeEnergy_le
    {K m1 m2 : Real} (hK : 0 <= K)
    (hm10 : 0 <= m1) (hm11 : m1 <= 1)
    (hm20 : 0 <= m2) (hm21 : m2 <= 1) :
    singleBondInterfaceFreeEnergy K m1 m2 <= 2 * K * (m1 * m2) := by
  let a := m1 * m2
  have ha0 : 0 <= a := mul_nonneg hm10 hm20
  have ha1 : a <= 1 := mul_le_one₀ hm11 hm20 hm21
  have ht0 : 0 <= Real.tanh K := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hK) (Real.cosh_pos K).le
  have ht1 : Real.tanh K < 1 := Real.tanh_lt_one K
  have hat : a * Real.tanh K ∈ Set.Icc (-1 : Real) 1 := by
    constructor
    · exact (mul_nonneg ha0 ht0).trans' (by norm_num)
    · exact (mul_le_of_le_one_left ht0 ha1).trans ht1.le
  have hart := artanh_mul_tanh_le_mul ha0 ha1 hK
  rw [Real.artanh_eq_half_log hat] at hart
  unfold singleBondInterfaceFreeEnergy
  change Real.log ((1 + a * Real.tanh K) / (1 - a * Real.tanh K)) <=
    2 * K * a
  nlinarith

end

end StatMech.Ising
