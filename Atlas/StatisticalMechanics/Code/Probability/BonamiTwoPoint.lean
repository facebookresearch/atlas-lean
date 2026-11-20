/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib

open Real Set

namespace StatMech.Probability







theorem bts_convexOn_rpow_nonpos {c : ℝ} (hc : c ≤ 0) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => x ^ c) := by
  have hD : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
  have hcont : ContinuousOn (fun x : ℝ => x ^ c) (Set.Ioi 0) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx; left; exact (Set.mem_Ioi.mp hx).ne'
  have hint : interior (Set.Ioi (0 : ℝ)) = Set.Ioi 0 := interior_Ioi
  apply convexOn_of_hasDerivWithinAt2_nonneg hD hcont
      (f' := fun x => c * x ^ (c - 1)) (f'' := fun x => c * (c - 1) * x ^ (c - 2))
  · intro x hx
    rw [hint] at hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    exact (Real.hasDerivAt_rpow_const (Or.inl hx0.ne')).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have h : HasDerivAt (fun y => c * y ^ (c - 1)) (c * ((c - 1) * x ^ (c - 1 - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hx0.ne')).const_mul c
    have heq : c * ((c - 1) * x ^ (c - 1 - 1)) = c * (c - 1) * x ^ (c - 2) := by ring_nf
    rw [heq] at h
    exact h.hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hpow : 0 ≤ x ^ (c - 2) := (Real.rpow_pos_of_pos hx0 _).le
    have hcc : 0 ≤ c * (c - 1) := by nlinarith
    positivity




theorem bts_two_le_sum {c t : ℝ} (hc : c ≤ 0) (ht : |t| < 1) :
    (2 : ℝ) ≤ (1 + t) ^ c + (1 - t) ^ c := by
  have h1 : (0 : ℝ) < 1 + t := by rw [abs_lt] at ht; linarith
  have h2 : (0 : ℝ) < 1 - t := by rw [abs_lt] at ht; linarith
  have hconv := bts_convexOn_rpow_nonpos hc
  have hmid := hconv.2 (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have hpt : (1 : ℝ) / 2 * (1 + t) + 1 / 2 * (1 - t) = 1 := by ring
  rw [hpt, Real.one_rpow] at hmid
  linarith










theorem bts_convexOn_g {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1)
      (fun t => (1 + t) ^ q + (1 - t) ^ q - 2 - q * (q - 1) * t ^ 2) := by
  have hD : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc _ _
  have hint : interior (Set.Icc (-1 : ℝ) 1) = Set.Ioo (-1) 1 := by rw [interior_Icc]
  have hcont : ContinuousOn
      (fun t : ℝ => (1 + t) ^ q + (1 - t) ^ q - 2 - q * (q - 1) * t ^ 2)
      (Set.Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    apply ContinuousOn.add
    · exact (continuousOn_const.add continuousOn_id).rpow_const
        (fun x _ => Or.inr (by linarith))
    · exact (continuousOn_const.sub continuousOn_id).rpow_const
        (fun x _ => Or.inr (by linarith))
    · exact continuousOn_const
    · exact continuousOn_const.mul (continuousOn_pow 2)
  apply convexOn_of_hasDerivWithinAt2_nonneg hD hcont
      (f' := fun t => q * (1 + t) ^ (q - 1) - q * (1 - t) ^ (q - 1) - 2 * (q * (q - 1)) * t)
      (f'' := fun t => q * (q - 1) * ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2))
        - 2 * (q * (q - 1)))
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have h1 : 0 < 1 + x := by linarith
    have h2 : 0 < 1 - x := by linarith
    have d1 : HasDerivAt (fun s => (1 + s) ^ q) (1 * q * (1 + x) ^ (q - 1)) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (Or.inl h1.ne')
    have d2 : HasDerivAt (fun s => (1 - s) ^ q) (-1 * q * (1 - x) ^ (q - 1)) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).rpow_const (Or.inl h2.ne')
    have d3 : HasDerivAt (fun t : ℝ => q * (q - 1) * t ^ 2) (q * (q - 1) * (2 * x)) x := by
      have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      simpa using h.const_mul (q * (q - 1))
    have D := ((d1.add d2).sub_const (2 : ℝ)).sub d3
    convert D.hasDerivWithinAt using 1
    ring
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have h1 : 0 < 1 + x := by linarith
    have h2 : 0 < 1 - x := by linarith
    have e1 : HasDerivAt (fun s => q * (1 + s) ^ (q - 1))
        (q * (1 * (q - 1) * (1 + x) ^ (q - 1 - 1))) x :=
      (((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (Or.inl h1.ne')).const_mul q
    have e2 : HasDerivAt (fun s => q * (1 - s) ^ (q - 1))
        (q * (-1 * (q - 1) * (1 - x) ^ (q - 1 - 1))) x :=
      (((hasDerivAt_id x).const_sub (1 : ℝ)).rpow_const (Or.inl h2.ne')).const_mul q
    have e3 : HasDerivAt (fun t : ℝ => 2 * (q * (q - 1)) * t) (2 * (q * (q - 1))) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * (q * (q - 1)))
    have E := (e1.sub e2).sub e3
    convert E.hasDerivWithinAt using 1
    rw [show q - 1 - 1 = q - 2 by ring]
    ring
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have habs : |x| < 1 := abs_lt.mpr ⟨hl, hr⟩
    have hsum := bts_two_le_sum (c := q - 2) (by linarith) habs
    have hcc : 0 ≤ q * (q - 1) := by nlinarith
    nlinarith [hsum, hcc]


theorem bts_even_convex_ge {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) g)
    (heven : ∀ t, g (-t) = g t) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    g 0 ≤ g t := by
  have htneg : -t ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨h1, h2⟩ := ht; constructor <;> [linarith; linarith]
  have hmid := hconv.2 ht htneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have hpt : (1 : ℝ) / 2 * t + 1 / 2 * (-t) = 0 := by ring
  rw [hpt, heven t] at hmid
  linarith



theorem bts_taylor_lower {q t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ht : |t| ≤ 1) :
    2 + q * (q - 1) * t ^ 2 ≤ (1 + t) ^ q + (1 - t) ^ q := by
  set g : ℝ → ℝ := fun s => (1 + s) ^ q + (1 - s) ^ q - 2 - q * (q - 1) * s ^ 2 with hg
  have hconv := bts_convexOn_g hq1 hq2
  have heven : ∀ s, g (-s) = g s := by
    intro s; simp only [hg]; rw [show (1 : ℝ) + -s = 1 - s by ring,
      show (1 : ℝ) - -s = 1 + s by ring, neg_pow]; ring
  have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
  have hge := bts_even_convex_ge hconv heven htmem
  simp only [add_zero, sub_zero, Real.one_rpow] at hge
  
  nlinarith [hge]










theorem bts_core {q t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 + (q - 1) * t ^ 2 ≤ (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  have htabs : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, ht1⟩
  
  have hfact2 := bts_taylor_lower hq1 hq2 htabs
  set M : ℝ := ((1 + t) ^ q + (1 - t) ^ q) / 2 with hM
  have hMlb : 1 + (q * (q - 1) / 2) * t ^ 2 ≤ M := by rw [hM]; nlinarith [hfact2]
  
  have hX : (0 : ℝ) ≤ 1 + (q - 1) * t ^ 2 := by nlinarith [sq_nonneg t]
  have hs : (-1 : ℝ) ≤ (q - 1) * t ^ 2 := by nlinarith [sq_nonneg t]
  have hbern := rpow_one_add_le_one_add_mul_self hs (by linarith : (0 : ℝ) ≤ q / 2)
      (by linarith : q / 2 ≤ 1)
  have hcoef : 1 + q / 2 * ((q - 1) * t ^ 2) = 1 + (q * (q - 1) / 2) * t ^ 2 := by ring
  rw [hcoef] at hbern
  have hstep : (1 + (q - 1) * t ^ 2) ^ (q / 2) ≤ M := le_trans hbern hMlb
  
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hstep
      (by positivity : (0 : ℝ) ≤ 2 / q)
  rwa [← Real.rpow_mul hX, show q / 2 * (2 / q) = 1 by field_simp, Real.rpow_one] at hmono





theorem bts_core' {q t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ 2 + (q - 1) ≤ (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) := by
  have core := bts_core hq1 hq2 ht0 ht1
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have slack : t ^ 2 + (q - 1) ≤ 1 + (q - 1) * t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t ^ 2) (by linarith : (0 : ℝ) ≤ 2 - q)]
  linarith






theorem bts_nonneg {q a b : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + (q - 1) * b ^ 2 ≤ ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  rcases le_total b a with hab | hab
  · 
    rcases eq_or_lt_of_le ha with rfl | ha0
    · 
      have hb0 : b = 0 := le_antisymm (by simpa using hab) hb
      subst hb0
      norm_num
      positivity
    · set t := b / a with ht
      have ht0 : 0 ≤ t := by rw [ht]; positivity
      have ht1 : t ≤ 1 := by rw [ht, div_le_one ha0]; exact hab
      have core2 := bts_core hq1 hq2 ht0 ht1
      have e1 : a + b = a * (1 + t) := by rw [ht]; field_simp
      have e2 : a - b = a * (1 - t) := by rw [ht]; field_simp
      have hab1 : |a + b| = a * (1 + t) := by rw [e1, abs_of_nonneg]; positivity
      have hab2 : |a - b| = a * (1 - t) := by
        rw [e2, abs_of_nonneg]
        have : 0 ≤ 1 - t := by linarith
        positivity
      rw [hab1, hab2, Real.mul_rpow ha (by linarith : (0 : ℝ) ≤ 1 + t),
        Real.mul_rpow ha (by linarith : (0 : ℝ) ≤ 1 - t)]
      have hfac : (a ^ q * (1 + t) ^ q + a ^ q * (1 - t) ^ q) / 2
          = a ^ q * (((1 + t) ^ q + (1 - t) ^ q) / 2) := by ring
      rw [hfac, Real.mul_rpow (Real.rpow_nonneg ha q) (by positivity),
        ← Real.rpow_mul ha, show q * (2 / q) = 2 by field_simp, Real.rpow_two]
      have hLHS : a ^ 2 + (q - 1) * b ^ 2 = a ^ 2 * (1 + (q - 1) * t ^ 2) := by
        rw [ht]; field_simp
      rw [hLHS]
      exact mul_le_mul_of_nonneg_left core2 (sq_nonneg a)
  · 
    rcases eq_or_lt_of_le hb with rfl | hb0
    · have ha0 : a = 0 := le_antisymm (by simpa using hab) ha
      subst ha0
      norm_num
      positivity
    · set t := a / b with ht
      have ht0 : 0 ≤ t := by rw [ht]; positivity
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hb0]; exact hab
      have core := bts_core' hq1 hq2 ht0 ht1
      have e1 : a + b = b * (1 + t) := by rw [ht]; field_simp; ring
      have e2 : a - b = b * (1 - t) * (-1) := by rw [ht]; field_simp; ring
      have hab1 : |a + b| = b * (1 + t) := by rw [e1, abs_of_nonneg]; positivity
      have hab2 : |a - b| = b * (1 - t) := by
        rw [e2, abs_mul, abs_neg, abs_one, mul_one, abs_of_nonneg]
        have : 0 ≤ 1 - t := by linarith
        positivity
      rw [hab1, hab2, Real.mul_rpow hb (by linarith : (0 : ℝ) ≤ 1 + t),
        Real.mul_rpow hb (by linarith : (0 : ℝ) ≤ 1 - t)]
      have hfac : (b ^ q * (1 + t) ^ q + b ^ q * (1 - t) ^ q) / 2
          = b ^ q * (((1 + t) ^ q + (1 - t) ^ q) / 2) := by ring
      rw [hfac, Real.mul_rpow (Real.rpow_nonneg hb q) (by positivity),
        ← Real.rpow_mul hb, show q * (2 / q) = 2 by field_simp, Real.rpow_two]
      have hLHS : a ^ 2 + (q - 1) * b ^ 2 = b ^ 2 * (t ^ 2 + (q - 1)) := by
        rw [ht]; field_simp
      rw [hLHS]
      exact mul_le_mul_of_nonneg_left core (sq_nonneg b)





theorem bts_abs_sum_eq (a b q : ℝ) :
    abs (|a| + |b|) ^ q + abs (|a| - |b|) ^ q = |a + b| ^ q + |a - b| ^ q := by
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a| + |b|)]
  have h : (|a| + |b| = |a + b| ∧ abs (|a| - |b|) = |a - b|)
      ∨ (|a| + |b| = |a - b| ∧ abs (|a| - |b|) = |a + b|) := by
    rcases abs_cases (a + b) with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
    rcases abs_cases (a - b) with ⟨e2, s2⟩ | ⟨e2, s2⟩ <;>
    rcases abs_cases a with ⟨ea, sa⟩ | ⟨ea, sa⟩ <;>
    rcases abs_cases b with ⟨eb, sb⟩ | ⟨eb, sb⟩ <;>
    rcases abs_cases (|a| - |b|) with ⟨ec, sc⟩ | ⟨ec, sc⟩ <;>
    rw [e1, e2, ec, ea, eb] at * <;>
    first
      | (left; exact ⟨by linarith, by linarith⟩)
      | (right; exact ⟨by linarith, by linarith⟩)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; ring









theorem bts_twoPointScalar {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a b : ℝ) :
    a ^ 2 + ρ ^ 2 * b ^ 2
      ≤ ((|a + b| ^ (1 + ρ ^ 2) + |a - b| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
  set q : ℝ := 1 + ρ ^ 2 with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith [sq_nonneg ρ]
  have hq2 : q ≤ 2 := by rw [hq]; nlinarith
  have hrho : ρ ^ 2 = q - 1 := by rw [hq]; ring
  rw [hrho]
  
  have key := bts_nonneg hq1 hq2 (abs_nonneg a) (abs_nonneg b)
  rw [sq_abs, sq_abs, bts_abs_sum_eq a b q] at key
  exact key



theorem bts_twoPointScalar_forall :
    ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ 1 → ∀ a b : ℝ,
      a ^ 2 + ρ ^ 2 * b ^ 2
        ≤ ((|a + b| ^ (1 + ρ ^ 2) + |a - b| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) :=
  fun _ h0 h1 a b => bts_twoPointScalar h0 h1 a b

end StatMech.Probability
