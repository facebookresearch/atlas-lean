/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierDensity





namespace StatMech.FrontierD

noncomputable section

open scoped Interval

theorem intervalIntegral_cos_int_mul (z : Int) :
    (∫ beta in -Real.pi..Real.pi, Real.cos ((z : Real) * beta)) =
      if z = 0 then 2 * Real.pi else 0 := by
  by_cases hz : z = 0
  · subst z
    simp
    ring
  · rw [if_neg hz]
    have hzReal : (z : Real) ≠ 0 := by exact_mod_cast hz
    have hscaled := intervalIntegral.mul_integral_comp_mul_left
      (a := -Real.pi) (b := Real.pi) (f := Real.cos) (z : Real)
    have hrhs :
        (∫ x in (z : Real) * (-Real.pi)..(z : Real) * Real.pi,
          Real.cos x) = 0 := by
      rw [integral_cos]
      have hpos : Real.sin ((z : Real) * Real.pi) = 0 :=
        Real.sin_int_mul_pi z
      have hneg : Real.sin ((z : Real) * (-Real.pi)) = 0 := by
        rw [show (z : Real) * (-Real.pi) =
          -((z : Real) * Real.pi) by ring, Real.sin_neg, hpos, neg_zero]
      rw [hpos, hneg, sub_zero]
    rw [hrhs] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left hzReal

theorem intervalIntegral_sin_int_mul (z : Int) :
    (∫ beta in -Real.pi..Real.pi, Real.sin ((z : Real) * beta)) = 0 := by
  by_cases hz : z = 0
  · subst z
    simp
  · have hzReal : (z : Real) ≠ 0 := by exact_mod_cast hz
    have hscaled := intervalIntegral.mul_integral_comp_mul_left
      (a := -Real.pi) (b := Real.pi) (f := Real.sin) (z : Real)
    have hrhs :
        (∫ x in (z : Real) * (-Real.pi)..(z : Real) * Real.pi,
          Real.sin x) = 0 := by
      rw [integral_sin]
      rw [show (z : Real) * (-Real.pi) =
        -((z : Real) * Real.pi) by ring, Real.cos_neg, sub_self]
    rw [hrhs] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left hzReal

theorem intervalIntegral_cos_nat_mul_mul_cos_nat_mul
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * beta) * Real.cos ((n : Real) * beta)) =
      if m = n then Real.pi else 0 := by
  let zdiff : Int := (m : Int) - (n : Int)
  let zsum : Int := (m : Int) + (n : Int)
  have hsum : zsum ≠ 0 := by
    dsimp [zsum]
    omega
  have hid (beta : Real) :
      2 * (Real.cos ((m : Real) * beta) *
          Real.cos ((n : Real) * beta)) =
        Real.cos ((zdiff : Real) * beta) +
          Real.cos ((zsum : Real) * beta) := by
    rw [show (zdiff : Real) * beta =
        (m : Real) * beta - (n : Real) * beta by
      dsimp [zdiff]
      push_cast
      ring,
      show (zsum : Real) * beta =
        (m : Real) * beta + (n : Real) * beta by
      dsimp [zsum]
      push_cast
      ring]
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hprodInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta) *
        Real.cos ((n : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hdiffInt : IntervalIntegrable
      (fun beta => Real.cos ((zdiff : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsumInt : IntervalIntegrable
      (fun beta => Real.cos ((zsum : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have htwo :
      2 * (∫ beta in -Real.pi..Real.pi,
        Real.cos ((m : Real) * beta) * Real.cos ((n : Real) * beta)) =
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((zdiff : Real) * beta)) +
      ∫ beta in -Real.pi..Real.pi,
        Real.cos ((zsum : Real) * beta) := by
    rw [<- intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_congr (fun beta _ => hid beta)]
    exact intervalIntegral.integral_add hdiffInt hsumInt
  rw [intervalIntegral_cos_int_mul zdiff,
    intervalIntegral_cos_int_mul zsum, if_neg hsum, add_zero] at htwo
  by_cases hmn : m = n
  · rw [if_pos hmn]
    have hdiff : zdiff = 0 := by
      dsimp [zdiff]
      omega
    rw [if_pos hdiff] at htwo
    linarith
  · rw [if_neg hmn]
    have hdiff : zdiff ≠ 0 := by
      dsimp [zdiff]
      omega
    rw [if_neg hdiff] at htwo
    linarith

theorem intervalIntegral_sin_nat_mul_mul_cos_nat_mul
    (m n : Nat) :
    (∫ beta in -Real.pi..Real.pi,
      Real.sin ((m : Real) * beta) * Real.cos ((n : Real) * beta)) = 0 := by
  let zdiff : Int := (m : Int) - (n : Int)
  let zsum : Int := (m : Int) + (n : Int)
  have hid (beta : Real) :
      2 * (Real.sin ((m : Real) * beta) *
          Real.cos ((n : Real) * beta)) =
        Real.sin ((zsum : Real) * beta) +
          Real.sin ((zdiff : Real) * beta) := by
    rw [show (zsum : Real) * beta =
        (m : Real) * beta + (n : Real) * beta by
      dsimp [zsum]
      push_cast
      ring,
      show (zdiff : Real) * beta =
        (m : Real) * beta - (n : Real) * beta by
      dsimp [zdiff]
      push_cast
      ring]
    rw [Real.sin_add, Real.sin_sub]
    ring
  have hsumInt : IntervalIntegrable
      (fun beta => Real.sin ((zsum : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hdiffInt : IntervalIntegrable
      (fun beta => Real.sin ((zdiff : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have htwo :
      2 * (∫ beta in -Real.pi..Real.pi,
        Real.sin ((m : Real) * beta) * Real.cos ((n : Real) * beta)) =
      (∫ beta in -Real.pi..Real.pi,
        Real.sin ((zsum : Real) * beta)) +
      ∫ beta in -Real.pi..Real.pi,
        Real.sin ((zdiff : Real) * beta) := by
    rw [<- intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_congr (fun beta _ => hid beta)]
    exact intervalIntegral.integral_add hsumInt hdiffInt
  rw [intervalIntegral_sin_int_mul, intervalIntegral_sin_int_mul,
    zero_add] at htwo
  linarith


theorem intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * (alpha - beta)) *
        Real.cos ((n : Real) * beta)) =
      if m = n then Real.pi * Real.cos ((m : Real) * alpha) else 0 := by
  have hcosInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta) *
        Real.cos ((n : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun beta => Real.sin ((m : Real) * beta) *
        Real.cos ((n : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hid (beta : Real) :
      Real.cos ((m : Real) * (alpha - beta)) *
          Real.cos ((n : Real) * beta) =
        Real.cos ((m : Real) * alpha) *
            (Real.cos ((m : Real) * beta) * Real.cos ((n : Real) * beta)) +
          Real.sin ((m : Real) * alpha) *
            (Real.sin ((m : Real) * beta) * Real.cos ((n : Real) * beta)) := by
    rw [mul_sub, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_congr (fun beta _ => hid beta)]
  rw [intervalIntegral.integral_add
    (hcosInt.const_mul _) (hsinInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral_cos_nat_mul_mul_cos_nat_mul hm hn,
    intervalIntegral_sin_nat_mul_mul_cos_nat_mul]
  by_cases hmn : m = n
  · simp [hmn]
    ring
  · simp [hmn]

end

end StatMech.FrontierD
