/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Code.Probability.BonamiTwoPoint

open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability







def pbt_g (p q z : ℝ) : ℝ :=
  ((1 - p) + p * z) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2





def pbt_OneVarCore (p q : ℝ) : Prop :=
  ∀ z : ℝ, 0 ≤ z → pbt_g p q z ≤ ((1 - p) + p * z ^ q) ^ (2 / q)




theorem pbt_g_at_one (p q : ℝ) : pbt_g p q 1 = 1 := by
  unfold pbt_g; ring




theorem pbt_core_at_one (p q : ℝ) :
    pbt_g p q 1 ≤ ((1 - p) + p * (1:ℝ) ^ q) ^ (2 / q) := by
  rw [pbt_g_at_one, Real.one_rpow]
  have h : ((1 - p) + p * 1 : ℝ) = 1 := by ring
  rw [h, Real.one_rpow]





theorem pbt_OneVarCore_q_one (p : ℝ) : pbt_OneVarCore p 1 := by
  intro z _
  unfold pbt_g
  simp only [sub_self, zero_mul, add_zero, Real.rpow_one]
  rw [show (2:ℝ) / 1 = 2 by norm_num, Real.rpow_two]







def pbt_lhs (p q u v : ℝ) : ℝ :=
  ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2




theorem pbt_coeff_slack {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    0 ≤ p * (1 - p) - (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 := by
  have h4 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have h4nn : 0 ≤ 4 * p * (1 - p) := by nlinarith
  have hpp : 0 ≤ p * (1 - p) := by nlinarith
  have hprod : (q - 1) * (4 * p * (1 - p)) ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q - 1) h4nn]
  nlinarith [mul_nonneg hpp (by linarith : (0:ℝ) ≤ 1 - (q - 1) * (4 * p * (1 - p)))]






theorem pbt_lhs_abs_mono {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (u v : ℝ) : pbt_lhs p q u v ≤ pbt_lhs p q |u| |v| := by
  have hslack := pbt_coeff_slack hp0 hp1 hq1 hq2
  have huv : u * v ≤ |u| * |v| := by
    calc u * v ≤ |u * v| := le_abs_self _
      _ = |u| * |v| := abs_mul u v
  have hu : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv : |v| ^ 2 = v ^ 2 := sq_abs v
  unfold pbt_lhs
  nlinarith [hslack, huv, hu, hv, sq_nonneg u, sq_nonneg v]






theorem pbt_value_pos_of_core {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q)
    (Hcore : pbt_OneVarCore p q) {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    pbt_lhs p q u v ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
  set z := v / u with hz
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have core := Hcore z hz0
  
  have hLHS : pbt_lhs p q u v = u ^ 2 * pbt_g p q z := by
    unfold pbt_lhs pbt_g
    rw [hz]; field_simp; ring
  
  have hzq : z ^ q = v ^ q / u ^ q := by
    rw [hz, Real.div_rpow hv (le_of_lt hu)]
  have hRHS : ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q)
      = u ^ 2 * ((1 - p) + p * z ^ q) ^ (2 / q) := by
    rw [hzq]
    have huq : (0:ℝ) < u ^ q := Real.rpow_pos_of_pos hu q
    have hfac : (1 - p) * u ^ q + p * v ^ q = u ^ q * ((1 - p) + p * (v ^ q / u ^ q)) := by
      field_simp
    have hbase : (0:ℝ) ≤ (1 - p) + p * (v ^ q / u ^ q) := by
      have : (0:ℝ) ≤ v ^ q / u ^ q := by positivity
      have hpv : (0:ℝ) ≤ p * (v ^ q / u ^ q) := by positivity
      linarith
    rw [hfac, Real.mul_rpow (le_of_lt huq) hbase]
    have hexp : q * (2 / q) = (2 : ℝ) := by
      field_simp
    have huq2 : (u ^ q) ^ (2 / q) = u ^ 2 := by
      rw [← Real.rpow_mul (le_of_lt hu), hexp, Real.rpow_two]
    rw [huq2]
  rw [hLHS, hRHS]
  exact mul_le_mul_of_nonneg_left core (sq_nonneg u)





theorem pbt_lhs_reflect (p q u v : ℝ) : pbt_lhs p q u v = pbt_lhs (1 - p) q v u := by
  unfold pbt_lhs; ring





theorem pbt_value_nonneg_of_core {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q)
    (Hcore : pbt_OneVarCore p q) (Hcore' : pbt_OneVarCore (1 - p) q)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    pbt_lhs p q u v ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · 
    rcases eq_or_lt_of_le hv with hv0 | hv0
    · 
      rw [← hu0, ← hv0]
      unfold pbt_lhs
      simp only [mul_zero, sub_zero, add_zero]
      rw [Real.zero_rpow (by linarith : q ≠ 0)]
      simp [Real.zero_rpow (show (2:ℝ)/q ≠ 0 by positivity)]
    · 
      rw [← hu0]
      rw [pbt_lhs_reflect p q 0 v]
      have key := pbt_value_pos_of_core (p := 1 - p) (by linarith) (by linarith) hq0 Hcore'
        (u := v) (v := 0) hv0 (le_refl 0)
      have hrhs : ((1 - (1 - p)) * v ^ q + (1 - p) * (0:ℝ) ^ q) ^ (2 / q)
          = ((1 - p) * (0:ℝ) ^ q + p * v ^ q) ^ (2 / q) := by
        rw [show (1:ℝ) - (1 - p) = p by ring]; ring_nf
      rw [hrhs] at key
      exact key
  · 
    exact pbt_value_pos_of_core hp0 hp1 hq0 Hcore hu0 hv
















theorem pbt_two_point_value_of_core {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (Hcore : pbt_OneVarCore p q) (Hcore' : pbt_OneVarCore (1 - p) q) (u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  have hstep1 : pbt_lhs p q u v ≤ pbt_lhs p q |u| |v| :=
    pbt_lhs_abs_mono hp0 hp1 hq1 hq2 u v
  have hstep2 : pbt_lhs p q |u| |v| ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) :=
    pbt_value_nonneg_of_core hp0 hp1 hq0 Hcore Hcore' (abs_nonneg u) (abs_nonneg v)
  have : pbt_lhs p q u v ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) :=
    le_trans hstep1 hstep2
  unfold pbt_lhs at this
  exact this








theorem pbt_core_half {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    pbt_OneVarCore (1 / 2) q := by
  intro z hz
  
  set ρ : ℝ := Real.sqrt (q - 1) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by rw [hρ]; rw [Real.sqrt_le_one]; linarith
  have hρsq : ρ ^ 2 = q - 1 := by
    rw [hρ, Real.sq_sqrt (by linarith)]
  
  have hqe : (1 : ℝ) + ρ ^ 2 = q := by rw [hρsq]; ring
  have hbts := bts_twoPointScalar hρ0 hρ1 ((1 + z) / 2) ((z - 1) / 2)
  rw [hqe] at hbts
  
  have ha : (1 + z) / 2 + (z - 1) / 2 = z := by ring
  have hb : (1 + z) / 2 - (z - 1) / 2 = 1 := by ring
  rw [ha, hb] at hbts
  
  rw [abs_of_nonneg hz, abs_one, Real.one_rpow] at hbts
  
  have hLHS : ((1 + z) / 2) ^ 2 + ρ ^ 2 * ((z - 1) / 2) ^ 2 = pbt_g (1 / 2) q z := by
    unfold pbt_g; rw [hρsq]; ring
  have hRHS : ((z ^ q + 1) / 2) ^ (2 / q) = ((1 - 1 / 2) + 1 / 2 * z ^ q) ^ (2 / q) := by
    congr 1; ring
  rw [hLHS, hRHS] at hbts
  exact hbts













theorem pbt_jensen_mean {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((1 - p) * u + p * v) ^ 2 ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  have hmnn : (0:ℝ) ≤ (1 - p) * u + p * v := by nlinarith
  have hbasenn : (0:ℝ) ≤ (1 - p) * u ^ q + p * v ^ q := by positivity
  
  have hconv : ((1 - p) * u + p * v) ^ q ≤ (1 - p) * u ^ q + p * v ^ q := by
    have hcvx := (convexOn_rpow hq1).2 (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hv)
      (by linarith : (0:ℝ) ≤ 1 - p) hp0 (by ring)
    simpa [smul_eq_mul] using hcvx
  
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hmnn q) hconv (by positivity : (0:ℝ) ≤ 2 / q)
  have hlhs : (((1 - p) * u + p * v) ^ q) ^ (2 / q) = ((1 - p) * u + p * v) ^ 2 := by
    rw [← Real.rpow_mul hmnn, show q * (2 / q) = (2:ℝ) by field_simp, Real.rpow_two]
  rwa [hlhs] at hmono








theorem pbt_residue_satisfiable :
    (∀ p, pbt_OneVarCore p 1) ∧ (∀ q, 1 ≤ q → q ≤ 2 → pbt_OneVarCore (1 / 2) q) :=
  ⟨pbt_OneVarCore_q_one, fun _ hq1 hq2 => pbt_core_half hq1 hq2⟩






theorem pbt_residue_noncirc {p q : ℝ} (H : pbt_OneVarCore p q) (z : ℝ) (hz : 0 ≤ z) :
    ((1 - p) + p * z) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2
      ≤ ((1 - p) + p * z ^ q) ^ (2 / q) :=
  H z hz



































def pbt_TensorisationTarget : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ q : ℝ, 1 ≤ q → q ≤ 2 →
    
    (pbt_OneVarCore p q ∧ pbt_OneVarCore (1 - p) q) →
    ∀ u v : ℝ,
      ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
        ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q)






theorem pbt_tensorisation_reduction : pbt_TensorisationTarget := by
  intro p hp0 hp1 q hq1 hq2 ⟨Hcore, Hcore'⟩ u v
  exact pbt_two_point_value_of_core (le_of_lt hp0) (le_of_lt hp1) hq1 hq2 Hcore Hcore' u v

end StatMech.Probability
