/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib

open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability









noncomputable def tpl_ent (p a b : ℝ) : ℝ :=
  (1 - p) * a * Real.log a + p * b * Real.log b
    - ((1 - p) * a + p * b) * Real.log ((1 - p) * a + p * b)


def tpl_mean (p a b : ℝ) : ℝ := (1 - p) * a + p * b






theorem tpl_ent_eq {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : 0 < b) :
    tpl_ent p a b
      = (1 - p) * a * Real.log (a / tpl_mean p a b)
        + p * b * Real.log (b / tpl_mean p a b) := by
  have hm : 0 < tpl_mean p a b := by
    unfold tpl_mean
    have : 0 < 1 - p := by linarith
    nlinarith [mul_pos this ha, mul_pos hp0 hb]
  unfold tpl_ent tpl_mean at *
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hm), Real.log_div (ne_of_gt hb) (ne_of_gt hm)]
  ring











theorem tpl_chiSq_bound {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a) (hb : 0 < b) :
    tpl_ent p a b ≤ p * (1 - p) * (a - b) ^ 2 / tpl_mean p a b := by
  have hm : 0 < tpl_mean p a b := by
    unfold tpl_mean
    have : 0 < 1 - p := by linarith
    nlinarith [mul_pos this ha, mul_pos hp0 hb]
  rw [tpl_ent_eq hp0 hp1 ha hb]
  set m := tpl_mean p a b with hmdef
  have hla : Real.log (a / m) ≤ a / m - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < a / m by positivity); linarith
  have hlb : Real.log (b / m) ≤ b / m - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < b / m by positivity); linarith
  have h1 : (1 - p) * a * Real.log (a / m) ≤ (1 - p) * a * (a / m - 1) :=
    mul_le_mul_of_nonneg_left hla (by nlinarith)
  have h2 : p * b * Real.log (b / m) ≤ p * b * (b / m - 1) :=
    mul_le_mul_of_nonneg_left hlb (by nlinarith)
  have hmval : m = (1 - p) * a + p * b := hmdef
  have key : (1 - p) * a * (a / m - 1) + p * b * (b / m - 1)
      = p * (1 - p) * (a - b) ^ 2 / m := by
    field_simp
    nlinarith [hmval]
  linarith [h1, h2]






theorem tpl_cauchy_schwarz {p x y : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p * (1 - p) * (x + y) ^ 2 ≤ (1 - p) * x ^ 2 + p * y ^ 2 := by
  nlinarith [sq_nonneg ((1 - p) * x - p * y)]








theorem tpl_var_div_mean_le {p g0 g1 : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpos : 0 < g0 ∨ 0 < g1) :
    p * (1 - p) * (g0 ^ 2 - g1 ^ 2) ^ 2 / ((1 - p) * g0 ^ 2 + p * g1 ^ 2)
      ≤ (g0 - g1) ^ 2 := by
  set m := (1 - p) * g0 ^ 2 + p * g1 ^ 2 with hmdef
  have h1p : 0 < 1 - p := by linarith
  have hm : 0 < m := by
    rw [hmdef]
    rcases hpos with h | h
    · nlinarith [mul_pos h1p (mul_pos h h), mul_nonneg hp0.le (sq_nonneg g1)]
    · nlinarith [mul_pos hp0 (mul_pos h h), mul_nonneg h1p.le (sq_nonneg g0)]
  have hab : g0 ^ 2 - g1 ^ 2 = (g0 - g1) * (g0 + g1) := by ring
  rw [div_le_iff₀ hm, hab,
    show p * (1 - p) * ((g0 - g1) * (g0 + g1)) ^ 2
        = (g0 - g1) ^ 2 * (p * (1 - p) * (g0 + g1) ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [hmdef]
  exact tpl_cauchy_schwarz hp0 hp1









theorem tpl_lsi_pos {p g0 g1 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 < g0) (h1 : 0 < g1) :
    tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
  have hchi := tpl_chiSq_bound hp0 hp1 (by positivity : 0 < g0 ^ 2) (by positivity : 0 < g1 ^ 2)
  have hcs := tpl_var_div_mean_le (g0 := g0) (g1 := g1) hp0 hp1 (Or.inl h0)
  have hmeq : tpl_mean p (g0 ^ 2) (g1 ^ 2) = (1 - p) * g0 ^ 2 + p * g1 ^ 2 := rfl
  rw [hmeq] at hchi
  linarith [hchi, hcs]




theorem tpl_boundary_scalar {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    -((1 - p) * Real.log (1 - p)) ≤ p := by
  have h1p : 0 < 1 - p := by linarith
  
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - p) by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt h1p), Real.log_one, zero_sub] at hlog
  
  have : -((1 - p) * Real.log (1 - p)) = (1 - p) * (- Real.log (1 - p)) := by ring
  rw [this]
  have hmul : (1 - p) * (- Real.log (1 - p)) ≤ (1 - p) * (1 / (1 - p) - 1) :=
    mul_le_mul_of_nonneg_left hlog h1p.le
  have hrw : (1 - p) * (1 / (1 - p) - 1) = p := by
    field_simp; ring
  linarith [hmul, hrw.le, hrw.ge]



theorem tpl_lsi_b_zero {p g0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ g0) :
    tpl_ent p (g0 ^ 2) 0 ≤ (g0 - 0) ^ 2 := by
  have h1p : 0 < 1 - p := by linarith
  rcases eq_or_lt_of_le h0 with h0z | h0pos
  · 
    rw [← h0z]; unfold tpl_ent; simp
  · 
    have hg0sq : 0 < g0 ^ 2 := by positivity
    
    
    have hmval : (1 - p) * g0 ^ 2 + p * 0 = (1 - p) * g0 ^ 2 := by ring
    have hent : tpl_ent p (g0 ^ 2) 0 = -((1 - p) * Real.log (1 - p)) * g0 ^ 2 := by
      unfold tpl_ent
      rw [hmval, Real.log_mul (ne_of_gt h1p) (ne_of_gt hg0sq)]
      simp only [mul_zero, Real.log_zero, add_zero]
      ring
    rw [hent, show (g0 - 0) ^ 2 = g0 ^ 2 by ring]
    have hsc := tpl_boundary_scalar hp0 hp1
    calc -((1 - p) * Real.log (1 - p)) * g0 ^ 2 ≤ p * g0 ^ 2 :=
          mul_le_mul_of_nonneg_right hsc (sq_nonneg g0)
      _ ≤ 1 * g0 ^ 2 := mul_le_mul_of_nonneg_right (le_of_lt hp1) (sq_nonneg g0)
      _ = g0 ^ 2 := one_mul _




theorem tpl_ent_swap (p a b : ℝ) : tpl_ent p a b = tpl_ent (1 - p) b a := by
  simp only [tpl_ent, show (1 : ℝ) - (1 - p) = p by ring]
  ring_nf



theorem tpl_lsi_a_zero {p g1 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h1 : 0 ≤ g1) :
    tpl_ent p 0 (g1 ^ 2) ≤ (0 - g1) ^ 2 := by
  rw [tpl_ent_swap, show (0 - g1) ^ 2 = (g1 - 0) ^ 2 by ring]
  exact tpl_lsi_b_zero (by linarith) (by linarith) h1














theorem tpl_lsi_nonneg {p g0 g1 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) :
    tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
  rcases eq_or_lt_of_le h0 with h0z | h0pos
  · rw [← h0z]; simpa using tpl_lsi_a_zero hp0 hp1 h1
  · rcases eq_or_lt_of_le h1 with h1z | h1pos
    · rw [← h1z]; simpa using tpl_lsi_b_zero hp0 hp1 h0
    · exact tpl_lsi_pos hp0 hp1 h0pos h1pos









theorem tpl_lsi {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (g0 g1 : ℝ) :
    tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
  have hbase := tpl_lsi_nonneg hp0 hp1 (abs_nonneg g0) (abs_nonneg g1)
  rw [sq_abs, sq_abs] at hbase
  refine hbase.trans ?_
  
  have hcross : g0 * g1 ≤ |g0| * |g1| := by
    calc g0 * g1 ≤ |g0 * g1| := le_abs_self _
      _ = |g0| * |g1| := abs_mul g0 g1
  nlinarith [hcross, sq_abs g0, sq_abs g1]









theorem tpl_lsi_weighted {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (g0 g1 : ℝ) :
    tpl_ent p (g0 ^ 2) (g1 ^ 2)
      ≤ (1 / (p * (1 - p))) * (p * (1 - p) * (g0 - g1) ^ 2) := by
  have h1p : 0 < 1 - p := by linarith
  have hppne : p * (1 - p) ≠ 0 := by positivity
  rw [show (1 / (p * (1 - p))) * (p * (1 - p) * (g0 - g1) ^ 2) = (g0 - g1) ^ 2 from by
    field_simp]
  exact tpl_lsi hp0 hp1 g0 g1






theorem tpl_ent_nonneg {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ tpl_ent p a b := by
  have hconv := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb)
    (by linarith : (0 : ℝ) ≤ 1 - p) hp0.le (by ring)
  simp only [smul_eq_mul] at hconv
  
  unfold tpl_ent
  nlinarith [hconv]






theorem tpl_chiSq {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : 0 < a ∨ 0 < b) :
    tpl_ent p a b ≤ p * (1 - p) * (a - b) ^ 2 / tpl_mean p a b := by
  have h1p : 0 < 1 - p := by linarith
  have hm : 0 < tpl_mean p a b := by
    unfold tpl_mean
    rcases hpos with h | h
    · nlinarith [mul_pos h1p h, mul_nonneg hp0.le hb]
    · nlinarith [mul_pos hp0 h, mul_nonneg h1p.le ha]
  rcases eq_or_lt_of_le ha with haz | hapos
  · 
    have hbpos : 0 < b := by
      rcases hpos with h | h
      · rw [← haz] at h; exact absurd h (lt_irrefl 0)
      · exact h
    rw [← haz]
    
    
    have hmval : tpl_mean p 0 b = p * b := by unfold tpl_mean; ring
    have hent : tpl_ent p 0 b = -(p * Real.log p) * b := by
      unfold tpl_ent
      rw [show (1 - p) * 0 + p * b = p * b by ring,
        Real.log_mul (ne_of_gt hp0) (ne_of_gt hbpos)]
      simp only [mul_zero, Real.log_zero, zero_add]
      ring
    rw [hent, hmval]
    
    rw [show p * (1 - p) * (0 - b) ^ 2 / (p * b) = (1 - p) * b from by field_simp; ring]
    
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / p by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hp0), Real.log_one, zero_sub] at hlog
    
    have hstep : -(p * Real.log p) ≤ 1 - p := by
      have : -(p * Real.log p) = p * (- Real.log p) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hlog hp0.le
      have hrw : p * (1 / p - 1) = 1 - p := by field_simp
      linarith [this, hrw.le, hrw.ge]
    nlinarith [hstep, hbpos.le]
  · rcases eq_or_lt_of_le hb with hbz | hbpos
    · 
      rw [← hbz]
      have hmval : tpl_mean p a 0 = (1 - p) * a := by unfold tpl_mean; ring
      have hent : tpl_ent p a 0 = -((1 - p) * Real.log (1 - p)) * a := by
        unfold tpl_ent
        rw [show (1 - p) * a + p * 0 = (1 - p) * a by ring,
          Real.log_mul (ne_of_gt h1p) (ne_of_gt hapos)]
        simp only [mul_zero, Real.log_zero, add_zero]
        ring
      rw [hent, hmval]
      rw [show p * (1 - p) * (a - 0) ^ 2 / ((1 - p) * a) = p * a from by field_simp; ring]
      have hsc := tpl_boundary_scalar hp0 hp1
      nlinarith [mul_le_mul_of_nonneg_right hsc hapos.le, hapos.le]
    · exact tpl_chiSq_bound hp0 hp1 hapos hbpos

end StatMech.Probability
