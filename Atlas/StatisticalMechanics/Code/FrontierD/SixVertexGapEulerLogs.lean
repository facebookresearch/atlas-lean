/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexGapLambertProduct
import Code.FrontierD.SixVertexDualGapAsymptotic

open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexEulerLog (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.log
    (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))


def sixVertexPlusEulerLog (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))

private theorem expEuler_eq_pow (t : ℝ) (n : ℕ) :
    Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)) =
      Real.exp (-2 * Real.pi * t) ^ (n + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem summable_expEuler {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))) := by
  have hq0 : 0 ≤ Real.exp (-2 * Real.pi * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * Real.pi * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have h := (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  exact h.congr (fun n => (expEuler_eq_pow t n).symm)

theorem summable_sixVertexEulerLog {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.log
      (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) := by
  have h := (summable_expEuler ht).neg
  simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable h

theorem summable_sixVertexPlusEulerLog {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.log
      (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) :=
  Real.summable_log_one_add_of_summable (summable_expEuler ht)

theorem sixVertexPlusEulerLog_eq_sub {t : ℝ} (ht : 0 < t) :
    sixVertexPlusEulerLog t = sixVertexEulerLog (2 * t) - sixVertexEulerLog t := by
  have ht2 : 0 < 2 * t := by positivity
  have hs2 := summable_sixVertexEulerLog ht2
  have hs1 := summable_sixVertexEulerLog ht
  rw [sixVertexPlusEulerLog, sixVertexEulerLog, sixVertexEulerLog, ← hs2.tsum_sub hs1]
  apply tsum_congr
  intro n
  let x := Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hp : 0 < 2 * Real.pi * t * (n + 1 : ℝ) := by positivity
    nlinarith
  have htwo : Real.exp (-2 * Real.pi * (2 * t) * (n + 1 : ℝ)) = x ^ 2 := by
    dsimp [x]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [htwo]
  have hm : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.ne'
  have hp : 1 + x ≠ 0 := by positivity
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
    Real.log_mul hm hp]
  ring


def sixVertexAlternatingPlusEulerLog (t : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))

theorem sixVertexAlternatingPlusEulerLog_eq {t : ℝ} (ht : 0 < t) :
    sixVertexAlternatingPlusEulerLog t =
      sixVertexPlusEulerLog t - 2 * sixVertexPlusEulerLog (2 * t) := by
  let f : ℕ → ℝ := fun n => Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  have hf : Summable f := summable_sixVertexPlusEulerLog ht
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hsplit := tsum_even_add_odd he ho
  have hodd : (∑' k : ℕ, f (2 * k + 1)) = sixVertexPlusEulerLog (2 * t) := by
    rw [sixVertexPlusEulerLog]
    apply tsum_congr
    intro k
    dsimp [f]
    congr 2
    congr 1
    push_cast
    ring
  rw [sixVertexAlternatingPlusEulerLog]
  change (∑' n : ℕ, (-1 : ℝ) ^ n * f n) = _
  have halt : (∑' n : ℕ, (-1 : ℝ) ^ n * f n) =
      (∑' k : ℕ, f (2 * k)) - ∑' k : ℕ, f (2 * k + 1) := by
    have hse : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k) * f (2 * k))
        (∑' k : ℕ, f (2 * k)) := by
      simpa using he.hasSum
    have hso : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) * f (2 * k + 1))
        (-∑' k : ℕ, f (2 * k + 1)) := by
      convert ho.hasSum.neg using 1
      ext k
      rw [pow_add, pow_mul]
      norm_num
    have hall : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n)
        ((∑' k : ℕ, f (2 * k)) + (-∑' k : ℕ, f (2 * k + 1))) :=
      HasSum.even_add_odd hse hso
    simpa only [sub_eq_add_neg] using hall.tsum_eq
  rw [halt, hodd]
  change (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) =
    sixVertexPlusEulerLog t at hsplit
  linarith

theorem sixVertexAlternatingPlusEulerLog_eq_euler {t : ℝ} (ht : 0 < t) :
    sixVertexAlternatingPlusEulerLog t =
      3 * sixVertexEulerLog (2 * t) - sixVertexEulerLog t -
        2 * sixVertexEulerLog (4 * t) := by
  rw [sixVertexAlternatingPlusEulerLog_eq ht,
    sixVertexPlusEulerLog_eq_sub ht,
    sixVertexPlusEulerLog_eq_sub (show 0 < 2 * t by positivity)]
  ring_nf

theorem sixVertexGapAlternatingLogSeries_eq_euler
    {lam : ℝ} (hlam : 0 < lam) :
    sixVertexGapAlternatingLogSeries lam =
      3 * sixVertexEulerLog (2 * (lam / Real.pi)) -
        sixVertexEulerLog (lam / Real.pi) -
        2 * sixVertexEulerLog (4 * (lam / Real.pi)) := by
  have ht : 0 < lam / Real.pi := div_pos hlam Real.pi_pos
  rw [← sixVertexAlternatingPlusEulerLog_eq_euler ht]
  rw [sixVertexGapAlternatingLogSeries, sixVertexAlternatingPlusEulerLog]
  apply tsum_congr
  intro n
  congr 3
  congr 1
  field_simp [Real.pi_ne_zero]



def sixVertexOddEulerRatioLog (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.log
    ((1 + Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ))) /
      (1 - Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ))))

theorem sixVertexOddEulerRatioLog_eq_euler {t : ℝ} (ht : 0 < t) :
    sixVertexOddEulerRatioLog t =
      3 * sixVertexEulerLog (2 * t) - 2 * sixVertexEulerLog t -
        sixVertexEulerLog (4 * t) := by
  let fm : ℕ → ℝ := fun n => Real.log
    (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  let fp : ℕ → ℝ := fun n => Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  have hfm : Summable fm := summable_sixVertexEulerLog ht
  have hfp : Summable fp := summable_sixVertexPlusEulerLog ht
  have hme : Summable (fun n => fm (2 * n)) := hfm.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hmo : Summable (fun n => fm (2 * n + 1)) := hfm.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hpe : Summable (fun n => fp (2 * n)) := hfp.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hpo : Summable (fun n => fp (2 * n + 1)) := hfp.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hmSplit := tsum_even_add_odd hme hmo
  have hpSplit := tsum_even_add_odd hpe hpo
  have hmOdd : (∑' n, fm (2 * n)) =
      sixVertexEulerLog t - sixVertexEulerLog (2 * t) := by
    have heven : (∑' n, fm (2 * n + 1)) = sixVertexEulerLog (2 * t) := by
      rw [sixVertexEulerLog]
      apply tsum_congr
      intro n
      dsimp [fm]
      congr 2
      congr 1
      push_cast
      ring
    rw [heven] at hmSplit
    change _ + sixVertexEulerLog (2 * t) = sixVertexEulerLog t at hmSplit
    exact eq_sub_of_add_eq hmSplit
  have hpOdd : (∑' n, fp (2 * n)) =
      sixVertexPlusEulerLog t - sixVertexPlusEulerLog (2 * t) := by
    have heven : (∑' n, fp (2 * n + 1)) = sixVertexPlusEulerLog (2 * t) := by
      rw [sixVertexPlusEulerLog]
      apply tsum_congr
      intro n
      dsimp [fp]
      congr 2
      congr 1
      push_cast
      ring
    rw [heven] at hpSplit
    change _ + sixVertexPlusEulerLog (2 * t) = sixVertexPlusEulerLog t at hpSplit
    exact eq_sub_of_add_eq hpSplit
  rw [sixVertexOddEulerRatioLog]
  have hratio : ∀ n : ℕ,
      Real.log
        ((1 + Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ))) /
          (1 - Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ)))) =
        fp (2 * n) - fm (2 * n) := by
    intro n
    dsimp [fp, fm]
    push_cast
    have hx : Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have hn : 0 < (2 * n + 1 : ℝ) := by positivity
      have hp : 0 < 2 * Real.pi * t * (2 * n + 1 : ℝ) := by positivity
      nlinarith
    rw [Real.log_div (by positivity) (sub_ne_zero.mpr hx.ne')]
  rw [tsum_congr hratio, hpe.tsum_sub hme, hpOdd, hmOdd,
    sixVertexPlusEulerLog_eq_sub ht,
    sixVertexPlusEulerLog_eq_sub (show 0 < 2 * t by positivity)]
  ring_nf

theorem sixVertexDualGapPowerSeries_exp_eq_oddEuler (t : ℝ) :
    sixVertexDualGapPowerSeries (Real.exp (-2 * Real.pi * t)) =
      4 * sixVertexOddEulerRatioLog t := by
  rw [sixVertexDualGapPowerSeries, sixVertexOddEulerRatioLog, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sixVertexDualGapPowerTerm]
  congr 3 <;> rw [← Real.exp_nat_mul] <;> congr 1 <;> push_cast <;> ring_nf

end

end StatMech.FrontierD
