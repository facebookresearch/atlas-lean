/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingCriticalMomentum
import Code.FrontierA.TriangularIsingSymbolBounds
import Code.Onsager.PhaseRegularity

open Filter MeasureTheory Topology

namespace StatMech.FrontierA

noncomputable section



theorem triangularIsingSymbol_pos_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    0 < triangularIsingSymbol beta beta (beta * J) p q := by
  have hzeroNe : triangularIsingSymbol beta beta (beta * J) 0 0 ≠ 0 := by
    intro hzero
    exact hcrit ((triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).1 hzero)
  have hzeroNonneg : 0 <= triangularIsingSymbol beta beta (beta * J) 0 0 := by
    rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
    positivity
  have hzeroPos : 0 < triangularIsingSymbol beta beta (beta * J) 0 0 :=
    lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
  have hs : 0 <= Real.sinh (2 * beta) :=
    (Real.sinh_pos_iff.mpr (by linarith)).le
  have hr : 0 <= Real.sinh (2 * (beta * J)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hA : 0 <= (1 - Real.cos p) + (1 - Real.cos q) := by
    nlinarith [Real.cos_le_one p, Real.cos_le_one q]
  have hB : 0 <= 1 - Real.cos (p + q) := by
    linarith [Real.cos_le_one (p + q)]
  have hexcess := triangularIsingSymbol_sub_zero beta (beta * J) p q
  have hexcessNonneg : 0 <=
      triangularIsingSymbol beta beta (beta * J) p q -
        triangularIsingSymbol beta beta (beta * J) 0 0 := by
    rw [hexcess]
    positivity
  linarith

theorem triangularIsing_logSymbol_analyticAt_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  exact triangularIsingSymbol_pos_of_nonnegative_noncritical
    hbeta hJ hcrit p q



theorem triangularIsing_logSymbol_analyticAt_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1)
    (p q : Real) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  apply triangularIsingSymbol_pos_of_third_le_neg hbeta
  nlinarith [mul_le_mul_of_nonneg_left hJ hbeta.le]



theorem triangularIsingSymbol_pos_at_root_of_ne_zero
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hp : |p| <= Real.pi) (hq : |q| <= Real.pi)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    0 < triangularIsingSymbol beta beta (beta * J) p q := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_triangularIsingSymbol_quadratic_lower_at_root hbeta hroot
  have hpq : 0 < p ^ 2 + q ^ 2 := by
    rcases hne with hp0 | hq0
    · nlinarith [sq_pos_of_ne_zero hp0]
    · nlinarith [sq_pos_of_ne_zero hq0]
  exact (mul_pos hc hpq).trans_le (hlower p q hp hq)



theorem triangularIsing_logSymbol_analyticAt_at_root_of_ne_zero
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hp : |p| <= Real.pi) (hq : |q| <= Real.pi)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  exact triangularIsingSymbol_pos_at_root_of_ne_zero
    hbeta hroot hp hq hne


theorem triangularIsingSymbol_quadratic_upper_at_root
    {beta J p q : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    triangularIsingSymbol beta beta (beta * J) p q <=
      (Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * (p ^ 2 + q ^ 2) := by
  let s := Real.sinh (2 * beta)
  let r := Real.sinh (2 * (beta * J))
  let A := (1 - Real.cos p) + (1 - Real.cos q)
  let B := 1 - Real.cos (p + q)
  have hs : 0 <= s := (Real.sinh_pos_iff.mpr (by linarith)).le
  have hA : A <= (p ^ 2 + q ^ 2) / 2 := by
    dsimp [A]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := p),
      Real.one_sub_sq_div_two_le_cos (x := q)]
  have hB0 : 0 <= B := by
    dsimp [B]
    linarith [Real.cos_le_one (p + q)]
  have hB : B <= (p + q) ^ 2 / 2 := by
    dsimp [B]
    linarith [Real.one_sub_sq_div_two_le_cos (x := p + q)]
  have hpq : (p + q) ^ 2 <= 2 * (p ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (p - q)]
  have hzero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hroot
  have hexcess := triangularIsingSymbol_sub_zero beta (beta * J) p q
  change triangularIsingSymbol beta beta (beta * J) p q -
      triangularIsingSymbol beta beta (beta * J) 0 0 = s * A + r * B at hexcess
  rw [hzero, sub_zero] at hexcess
  rw [hexcess]
  have hSA : s * A <= s * ((p ^ 2 + q ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hA hs
  have hrB : r * B <= |r| * B :=
    mul_le_mul_of_nonneg_right (le_abs_self r) hB0
  have habs : 0 <= |r| := abs_nonneg r
  have hrB' : r * B <= |r| * (p ^ 2 + q ^ 2) := by
    calc
      r * B <= |r| * B := hrB
      _ <= |r| * ((p + q) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hB habs
      _ <= |r| * (p ^ 2 + q ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hpq habs]
  dsimp [s, r] at hSA hrB' ⊢
  nlinarith

theorem triangularIsingCriticalUpperCoefficient_pos
    {beta J : Real} (hbeta : 0 < beta) :
    0 < Real.sinh (2 * beta) / 2 +
      |Real.sinh (2 * (beta * J))| := by
  have hs : 0 < Real.sinh (2 * beta) :=
    Real.sinh_pos_iff.mpr (by linarith)
  positivity


def triangularIsingCriticalInverseSymbol
    (beta J p q : Real) : Real :=
  1 / triangularIsingSymbol beta beta (beta * J) p q


theorem triangularIsingCriticalInverseSymbol_lower_on_wedge
    {beta J x y : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hx : 0 < x) (h2xPi : 2 * x <= Real.pi)
    (hxy : x <= y) (hy2x : y <= 2 * x) :
    1 / ((Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * 5 * x ^ 2) <=
      triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  have hxPi : |x| <= Real.pi := by rw [abs_of_pos hx]; linarith
  have hy0 : 0 < y := hx.trans_le hxy
  have hyPi : |y| <= Real.pi := by rw [abs_of_pos hy0]; linarith
  have hs : 0 < triangularIsingSymbol beta beta (beta * J) x y :=
    triangularIsingSymbol_pos_at_root_of_ne_zero
      hbeta hroot hxPi hyPi (Or.inl hx.ne')
  have hu := triangularIsingSymbol_quadratic_upper_at_root
    (p := x) (q := y) hbeta hroot
  change triangularIsingSymbol beta beta (beta * J) x y <=
    C * (x ^ 2 + y ^ 2) at hu
  have hySq : y ^ 2 <= 4 * x ^ 2 := by nlinarith
  have hupper : triangularIsingSymbol beta beta (beta * J) x y <=
      C * 5 * x ^ 2 := by
    calc
      triangularIsingSymbol beta beta (beta * J) x y <=
          C * (x ^ 2 + y ^ 2) := hu
      _ <= C * 5 * x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hySq hC.le]
  unfold triangularIsingCriticalInverseSymbol
  exact one_div_le_one_div_of_le hs hupper


theorem triangularIsingCriticalInverseSymbol_inner_lower
    {beta J x : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hx : 0 < x) (h2xPi : 2 * x <= Real.pi) :
    1 / ((Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * 5 * x) <=
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hx2x : x <= 2 * x := by linarith
  have hconst : IntervalIntegrable (fun _y : Real => 1 / (C * 5 * x ^ 2))
      MeasureTheory.volume x (2 * x) := continuousOn_const.intervalIntegrable
  have hkernelCont : ContinuousOn
      (fun y : Real => triangularIsingCriticalInverseSymbol beta J x y)
      (Set.uIcc x (2 * x)) := by
    unfold triangularIsingCriticalInverseSymbol
    apply ContinuousOn.div continuousOn_const
        (by unfold triangularIsingSymbol; fun_prop)
    · intro y hy
      rw [Set.uIcc_of_le hx2x] at hy
      have hxPi : |x| <= Real.pi := by rw [abs_of_pos hx]; linarith
      have hy0 : 0 < y := hx.trans_le hy.1
      have hyPi : |y| <= Real.pi := by
        rw [abs_of_pos hy0]
        exact hy.2.trans h2xPi
      exact (triangularIsingSymbol_pos_at_root_of_ne_zero
        hbeta hroot hxPi hyPi (Or.inl hx.ne')).ne'
  have hkernel : IntervalIntegrable
      (fun y : Real => triangularIsingCriticalInverseSymbol beta J x y)
      MeasureTheory.volume x (2 * x) :=
    hkernelCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hconst hkernel
    (fun y hy => triangularIsingCriticalInverseSymbol_lower_on_wedge
      hbeta hroot hx h2xPi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  change 1 / (C * 5 * x) <= _
  convert hmono using 1
  field_simp
  ring



def triangularIsingCriticalInverseSymbolClamp
    (beta J c epsilon p q : Real) : Real :=
  1 / max (triangularIsingSymbol beta beta (beta * J) p q)
    (c * epsilon ^ 2)

theorem triangularIsingCriticalInverseSymbolClamp_continuous
    {beta J c epsilon : Real} (hc : 0 < c) (hepsilon : 0 < epsilon) :
    Continuous (Function.uncurry
      (triangularIsingCriticalInverseSymbolClamp beta J c epsilon)) := by
  have hs := continuous_triangularIsingSymbol beta beta (beta * J)
  have hm : Continuous (fun z : Real × Real =>
      max (triangularIsingSymbol beta beta (beta * J) z.1 z.2)
        (c * epsilon ^ 2)) := hs.max continuous_const
  apply Continuous.div continuous_const hm
  intro z
  have hcut : 0 < c * epsilon ^ 2 := mul_pos hc (sq_pos_of_pos hepsilon)
  exact ne_of_gt (hcut.trans_le (le_max_right _ _))

theorem triangularIsingCriticalInverseSymbolClamp_eq
    {beta J c epsilon p q : Real} (hc : 0 < c)
    (hsize : epsilon ^ 2 <= p ^ 2 + q ^ 2)
    (hlower : c * (p ^ 2 + q ^ 2) <=
      triangularIsingSymbol beta beta (beta * J) p q) :
    triangularIsingCriticalInverseSymbolClamp beta J c epsilon p q =
      triangularIsingCriticalInverseSymbol beta J p q := by
  have hcut : c * epsilon ^ 2 <=
      triangularIsingSymbol beta beta (beta * J) p q :=
    (mul_le_mul_of_nonneg_left hsize hc.le).trans hlower
  rw [triangularIsingCriticalInverseSymbolClamp,
    triangularIsingCriticalInverseSymbol, max_eq_left hcut]



theorem triangularIsingCriticalInverseSymbol_inner_continuousOn
    {beta J epsilon : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hepsilon : 0 < epsilon) :
    ContinuousOn (fun x : Real =>
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y)
      (Set.Icc epsilon 1) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_triangularIsingSymbol_quadratic_lower_at_root hbeta hroot
  let F : Real -> Real -> Real :=
    triangularIsingCriticalInverseSymbolClamp beta J c epsilon
  have hF : Continuous (Function.uncurry F) := by
    exact triangularIsingCriticalInverseSymbolClamp_continuous hc hepsilon
  have hmoving : Continuous (fun x : Real => ∫ y in x..(2 * x), F x y) :=
    StatMech.Onsager.ons_wedgeIntegral_continuous hF
  apply hmoving.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by linarith [hepsilon.trans_le hx.1])] at hy
  have hx0 : 0 < x := hepsilon.trans_le hx.1
  have hy0 : 0 < y := hx0.trans_le hy.1
  have hxPi : |x| <= Real.pi := by
    rw [abs_of_pos hx0]
    exact hx.2.trans (by linarith [Real.pi_gt_three])
  have hyPi : |y| <= Real.pi := by
    rw [abs_of_pos hy0]
    have hyTwo : y <= 2 := hy.2.trans (by nlinarith [hx.2])
    exact hyTwo.trans (by linarith [Real.pi_gt_three])
  have hsize : epsilon ^ 2 <= x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg y, mul_self_le_mul_self hepsilon.le hx.1]
  exact (triangularIsingCriticalInverseSymbolClamp_eq hc
    hsize (hlower x y hxPi hyPi)).symm



theorem triangularIsingCriticalInverseSymbol_wedge_lower
    {beta J epsilon : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon <= 1) :
    (1 / (2 * (Real.sinh (2 * beta) / 2 +
        |Real.sinh (2 * (beta * J))|))) *
        ((2 / 5 : Real) * Real.log (1 / epsilon)) <=
      ∫ x in epsilon..1,
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  have hcompCont : ContinuousOn (fun x : Real => 1 / (C * 5 * x))
      (Set.uIcc epsilon 1) := by
    rw [Set.uIcc_of_le hepsilonOne]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact mul_ne_zero (mul_ne_zero hC.ne' (by norm_num))
      (ne_of_gt (hepsilon.trans_le hx.1))
  have hcomp : IntervalIntegrable (fun x : Real => 1 / (C * 5 * x))
      MeasureTheory.volume epsilon 1 := hcompCont.intervalIntegrable
  have hinnerCont :=
    triangularIsingCriticalInverseSymbol_inner_continuousOn
      hbeta hroot hepsilon
  have hinner : IntervalIntegrable (fun x : Real =>
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y)
      MeasureTheory.volume epsilon 1 := by
    have hinnerCont' : ContinuousOn (fun x : Real =>
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y)
        (Set.uIcc epsilon 1) := by
      simpa [Set.uIcc_of_le hepsilonOne] using hinnerCont
    exact hinnerCont'.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hcomp hinner
    (fun x hx => triangularIsingCriticalInverseSymbol_inner_lower
      hbeta hroot (hepsilon.trans_le hx.1)
        (by linarith [hx.2, Real.pi_gt_three]))
  have hcompEq :
      (∫ x in epsilon..1, 1 / (C * 5 * x)) =
        (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by
    calc
      (∫ x in epsilon..1, 1 / (C * 5 * x)) =
          (1 / (2 * C)) * ∫ x in epsilon..1, 2 / (5 * x) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : x ≠ 0 := by
              rw [Set.uIcc_of_le hepsilonOne] at hx
              exact (ne_of_gt (hepsilon.trans_le hx.1))
            field_simp
      _ = (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by
        rw [StatMech.Onsager.ons_logKernel_integral hepsilon hepsilonOne]
        ring
  rw [hcompEq] at hmono
  change (1 / (2 * C)) * ((2 / 5 : Real) * Real.log (1 / epsilon)) <= _
  calc
    (1 / (2 * C)) * ((2 / 5 : Real) * Real.log (1 / epsilon)) =
        (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by ring
    _ <= _ := hmono



theorem triangularIsingCriticalInverseSymbol_wedge_tendsto
    {beta J : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    Tendsto (fun n : Nat =>
      ∫ x in Real.exp (-(n : Real))..1,
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y)
      atTop atTop := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  apply Filter.tendsto_atTop_mono (fun n =>
    triangularIsingCriticalInverseSymbol_wedge_lower hbeta hroot
      (Real.exp_pos _) (by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (Nat.cast_nonneg n)))
  have hlog := StatMech.Onsager.ons_logKernel_cutoff_tendsto 1 zero_lt_one
  have hscale := hlog.const_mul_atTop
    (show 0 < 1 / (2 * C) by positivity)
  simpa [C] using hscale

end

end StatMech.FrontierA
