/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! # McDiarmid's inequality on finite product spaces

The bounded-differences inequality with non-identical marginals:
for a function `f` on a finite product space whose one-coordinate
changes are bounded by `c i`, the upper tail around the
product-weight mean is at most `exp (-2 t^2 / ∑ c i ^ 2)`, and the
two-sided bound is twice that. This generalizes the finite iid form
in `MathlibExt/Probability/McDiarmid.lean` and covers roadmap
package ML-09 of the Atlas TCS canon roadmap.

Source: C. McDiarmid, "On the method of bounded differences"
(1989); Dubhashi and Panconesi, Concentration of Measure for the
Analysis of Randomized Algorithms (2009), Chapter 1.
-/

open Finset

open scoped NNReal in
private theorem finite_hoeffding {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (g : ι → ℝ) (c : ℝ)
    (hbd : ∀ a a', |g a - g a'| ≤ c) (s : ℝ) :
    ∑ a, p a * Real.exp (s * (g a - ∑ b, p b * g b))
      ≤ Real.exp (s ^ 2 * c ^ 2 / 8) := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty :=
    Finset.univ_nonempty_iff.mpr inferInstance
  obtain ⟨a_min, _, h_min⟩ := Finset.exists_min_image Finset.univ g hne
  obtain ⟨a_max, _, h_max⟩ := Finset.exists_max_image Finset.univ g hne
  have hle : ∀ a : ι, g a_min ≤ g a ∧ g a ≤ g a_max :=
    fun a => ⟨h_min a (Finset.mem_univ a), h_max a (Finset.mem_univ a)⟩
  have hAB : g a_min ≤ g a_max := (hle a_max).1
  have hBA0 : 0 ≤ g a_max - g a_min := sub_nonneg.mpr hAB
  have hBA : g a_max - g a_min ≤ c :=
    (le_abs_self _).trans (hbd a_max a_min)
  letI : MeasurableSpace ι := ⊤
  set μ : MeasureTheory.Measure ι :=
    ∑ a ∈ Finset.univ, ENNReal.ofReal (p a) • MeasureTheory.Measure.dirac a with hμ_def
  haveI hprob : MeasureTheory.IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_def, MeasureTheory.Measure.finsetSum_apply]
    simp only [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.dirac_apply, Set.indicator_univ, Pi.one_apply,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp_nonneg a), hp_sum,
      ENNReal.ofReal_one]
  have hm : AEMeasurable g μ := Measurable.of_discrete.aemeasurable
  have hb : ∀ᵐ a ∂μ, g a ∈ Set.Icc (g a_min) (g a_max) := by
    rw [hμ_def, MeasureTheory.ae_finsetSum_measure_iff]
    intro a _
    apply MeasureTheory.Measure.ae_smul_measure _ _
    rw [MeasureTheory.ae_dirac_iff MeasurableSet.of_discrete]
    exact ⟨(hle a).1, (hle a).2⟩
  have hint : ∀ f : ι → ℝ, (∫ a, f a ∂μ) = ∑ a, p a • f a := by
    intro f
    rw [hμ_def, MeasureTheory.integral_finsetSum_measure (fun a _ =>
      ((MeasureTheory.integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top))]
    apply Finset.sum_congr rfl
    intro a _
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
      ENNReal.toReal_ofReal (hp_nonneg a)]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (X := g) (μ := μ)
    (a := g a_min) (b := g a_max) hm hb
  have hmgf := hsub.mgf_le s
  have hmean : (∫ x, g x ∂μ) = ∑ b, p b * g b := by
    rw [hint g]
    simp [smul_eq_mul]
  rw [hmean] at hmgf
  have hmgf2 : (∫ a, Real.exp (s * (g a - ∑ b, p b * g b)) ∂μ)
      ≤ Real.exp ((((((‖g a_max - g a_min‖₊ / 2) ^ 2 : NNReal)) : ℝ) * s ^ 2 / 2)) := hmgf
  rw [hint] at hmgf2
  simp only [smul_eq_mul] at hmgf2
  refine hmgf2.trans (Real.exp_le_exp.mpr ?_)
  have hPd : ((((‖g a_max - g a_min‖₊ / 2) ^ 2 : NNReal)) : ℝ)
      = ((g a_max - g a_min) / 2) ^ 2 := by
    have h1 : ((‖g a_max - g a_min‖₊ : NNReal) : ℝ) = g a_max - g a_min := by
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hBA0]
    simp only [NNReal.coe_pow, NNReal.coe_div] at *
    rw [h1]
    simp
  rw [hPd]
  have hsq : (g a_max - g a_min) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hBA0 hBA 2
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg s)
  have e1 : ((g a_max - g a_min) / 2) ^ 2 * s ^ 2 / 2
      = (g a_max - g a_min) ^ 2 * s ^ 2 / 8 := by ring
  have e2 : s ^ 2 * c ^ 2 / 8 = c ^ 2 * s ^ 2 / 8 := by ring
  rw [e1, e2]
  linarith [hmul]

private theorem mgf_bound : ∀ (n : ℕ) (α : Fin n → Type*) [∀ i, Fintype (α i)]
    [∀ i, Nonempty (α i)]
    (p : ∀ i, α i → ℝ) (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ)
    (s : ℝ)
    (hbd : ∀ (i : Fin n) (x y : ∀ i, α i),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i),
    ∑ x, (∏ i, p i (x i)) * Real.exp (s * (f x - ∑ y, (∏ i, p i (y i)) * f y))
      ≤ Real.exp (s ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro α _ _ p hp_nonneg hp_sum f c s hbd
    have hw : ∀ x : (∀ i : Fin 0, α i), (∏ i, p i (x i)) = 1 :=
      fun x => Fin.prod_univ_zero _
    simp only [hw, one_mul]
    have hμ : (∑ y : ∀ i : Fin 0, α i, f y) = f default := Fintype.sum_unique _
    rw [hμ]
    rw [Fintype.sum_unique (fun x => Real.exp (s * (f x - f default)))]
    rw [Fin.sum_univ_zero]
    simp
  | succ m ih =>
    intro α instF instN p hp_nonneg hp_sum f c s hbd
    classical
    letI hfin' : ∀ i : Fin m, Fintype (α i.succ) := fun i => instF i.succ
    letI hne' : ∀ i : Fin m, Nonempty (α i.succ) := fun i => instN i.succ
    set μ0 : (∀ i : Fin m, α i.succ) → ℝ :=
      fun r => ∑ a0, p 0 a0 * f (Fin.cons a0 r) with hμ0_def
    have hμ0_eq : ∀ r, μ0 r = ∑ a0, p 0 a0 * f (Fin.cons a0 r) := fun r => rfl
    have hreindex : ∀ G : (∀ i : Fin (m + 1), α i) → ℝ,
        (∑ x, G x) = ∑ a0, ∑ r, G (Fin.cons a0 r) := by
      intro G
      have h1 := ((Fin.consEquiv α).sum_comp G).symm
      rw [Fintype.sum_prod_type] at h1
      exact h1
    have hw : ∀ (a0 : α 0) (r : ∀ i : Fin m, α i.succ),
        (∏ i, p i (Fin.cons a0 r i)) = p 0 a0 * ∏ i, p i.succ (r i) := by
      intro a0 r
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hμ : (∑ y, (∏ i, p i (y i)) * f y)
        = ∑ r, (∏ i, p i.succ (r i)) * μ0 r := by
      rw [hreindex]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      calc ∑ a0, (∏ i, p i (Fin.cons a0 r i)) * f (Fin.cons a0 r)
          = ∑ a0, (∏ i, p i.succ (r i)) * (p 0 a0 * f (Fin.cons a0 r)) := by
            apply Finset.sum_congr rfl
            intro a0 _
            rw [hw]
            ring
        _ = (∏ i, p i.succ (r i)) * μ0 r := by
            rw [← Finset.mul_sum]
    have hbd' : ∀ (i : Fin m) (r r' : ∀ i : Fin m, α i.succ),
        (∀ j, j ≠ i → r j = r' j) → |μ0 r - μ0 r'| ≤ c i.succ := by
      intro i r r' hrr'
      have hdiff : (μ0 r - μ0 r')
          = ∑ a0, p 0 a0 * (f (Fin.cons a0 r) - f (Fin.cons a0 r')) := by
        rw [hμ0_eq r, hμ0_eq r', ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a0 _
        ring
      rw [hdiff]
      have hnorm := norm_sum_le Finset.univ
        (fun a0 => p 0 a0 * (f (Fin.cons a0 r) - f (Fin.cons a0 r')))
      simp only [Real.norm_eq_abs] at hnorm
      refine hnorm.trans ?_
      calc ∑ a0, |p 0 a0 * (f (Fin.cons a0 r) - f (Fin.cons a0 r'))|
          = ∑ a0, p 0 a0 * |f (Fin.cons a0 r) - f (Fin.cons a0 r')| := by
            apply Finset.sum_congr rfl
            intro a0 _
            rw [abs_mul, abs_of_nonneg (hp_nonneg 0 a0)]
        _ ≤ ∑ a0, p 0 a0 * c i.succ := by
            apply Finset.sum_le_sum
            intro a0 _
            apply mul_le_mul_of_nonneg_left _ (hp_nonneg 0 a0)
            apply hbd i.succ (Fin.cons a0 r) (Fin.cons a0 r')
            intro j hj
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
            · rw [Fin.cons_zero, Fin.cons_zero]
            · rw [Fin.cons_succ, Fin.cons_succ]
              apply hrr' k
              intro hki
              apply hj
              rw [hki]
        _ = c i.succ := by
            rw [← Finset.sum_mul, hp_sum 0, one_mul]
    have hbd0 : ∀ (r : ∀ i : Fin m, α i.succ) (a a' : α 0),
        |f (Fin.cons a r) - f (Fin.cons a' r)| ≤ c 0 := by
      intro r a a'
      apply hbd 0 (Fin.cons a r) (Fin.cons a' r)
      intro j hj
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact absurd rfl hj
      · rw [Fin.cons_succ, Fin.cons_succ]
    have hinner : ∀ r : (∀ i : Fin m, α i.succ),
        (∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r)
          - (∑ y, (∏ i, p i (y i)) * f y))))
        ≤ Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
          * Real.exp (s ^ 2 * (c 0) ^ 2 / 8) := by
      intro r
      have hfactor : ∀ a0 : α 0,
          p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))
          = Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
            * (p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - μ0 r))) := by
        intro a0
        have hexp : s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y))
            = s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y))
              + s * (f (Fin.cons a0 r) - μ0 r) := by ring
        rw [hexp, Real.exp_add]
        ring
      calc ∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))
          = ∑ a0, Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
              * (p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - μ0 r))) := by
            apply Finset.sum_congr rfl
            intro a0 _
            exact hfactor a0
        _ = Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
              * ∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - μ0 r)) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
              * Real.exp (s ^ 2 * (c 0) ^ 2 / 8) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
            have hH := finite_hoeffding (p 0) (hp_nonneg 0) (hp_sum 0)
              (fun a0 => f (Fin.cons a0 r)) (c 0) (hbd0 r) s
            exact hH
    have hM : (∑ x, (∏ i, p i (x i)) * Real.exp (s * (f x - (∑ y, (∏ i, p i (y i)) * f y))))
        = ∑ r, (∏ i, p i.succ (r i))
          * (∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))) := by
      rw [hreindex, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      calc ∑ a0, (∏ i, p i (Fin.cons a0 r i)) * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))
          = ∑ a0, (∏ i, p i.succ (r i))
              * (p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))) := by
            apply Finset.sum_congr rfl
            intro a0 _
            rw [hw]
            ring
        _ = (∏ i, p i.succ (r i))
              * (∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y)))) := by
            rw [Finset.mul_sum]
    rw [hM]
    have hw'nonneg : ∀ r : (∀ i : Fin m, α i.succ), 0 ≤ ∏ i, p i.succ (r i) := by
      intro r
      apply Finset.prod_nonneg
      intro i _
      exact hp_nonneg i.succ (r i)
    calc ∑ r, (∏ i, p i.succ (r i))
            * (∑ a0, p 0 a0 * Real.exp (s * (f (Fin.cons a0 r) - (∑ y, (∏ i, p i (y i)) * f y))))
        ≤ ∑ r, (∏ i, p i.succ (r i))
            * (Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y)))
              * Real.exp (s ^ 2 * (c 0) ^ 2 / 8)) := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_left (hinner r) (hw'nonneg r)
      _ = Real.exp (s ^ 2 * (c 0) ^ 2 / 8)
            * ∑ r, (∏ i, p i.succ (r i))
              * Real.exp (s * (μ0 r - (∑ y, (∏ i, p i (y i)) * f y))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
      _ ≤ Real.exp (s ^ 2 * (c 0) ^ 2 / 8) * Real.exp (s ^ 2 * (∑ i : Fin m, (c i.succ) ^ 2) / 8) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          have hIH := @ih (fun i : Fin m => α i.succ) hfin' hne' (fun i a => p i.succ a)
            (fun i a => hp_nonneg i.succ a) (fun i => hp_sum i.succ)
            μ0 (fun i : Fin m => c i.succ) s hbd'
          rw [← hμ] at hIH
          exact hIH
      _ = Real.exp (s ^ 2 * (∑ i, c i ^ 2) / 8) := by
          have hV : (∑ i, c i ^ 2) = (c 0) ^ 2 + ∑ i : Fin m, (c i.succ) ^ 2 :=
            Fin.sum_univ_succ (fun i => c i ^ 2)
          rw [hV]
          rw [← Real.exp_add]
          congr 1
          ring

/-- McDiarmid's bounded-differences inequality on a finite product
space with non-identical marginals (one-sided form): if changing one
coordinate of `f` changes its value by at most `c i`, then the upper
tail of `f` around its mean is sub-Gaussian with variance proxy
`∑ i, c i ^ 2`. The mean and the tail probability are written with
the product weights `∏ i, p i (x i)`. -/
theorem mcdiarmid_product {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    [∀ i, Nonempty (α i)]
    (p : ∀ i, α i → ℝ) (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < ∑ i, c i ^ 2) (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : ∀ i, α i),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    (∑ x ∈ Finset.univ.filter
        (fun x => t ≤ f x - ∑ y, (∏ i, p i (y i)) * f y),
        ∏ i, p i (x i)) ≤ Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by

  classical
  set μ : ℝ := ∑ y, (∏ i, p i (y i)) * f y with hμ_def
  set V : ℝ := ∑ i, c i ^ 2 with hV_def
  have hspos : 0 < 4 * t / V := by
    apply div_pos _ hc_pos
    apply mul_pos _ ht
    norm_num
  have hM := mgf_bound n α p hp_nonneg hp_sum f c (4 * t / V) hbd
  simp only [← hμ_def, ← hV_def] at hM
  have hw_nonneg : ∀ x : (∀ i, α i), 0 ≤ ∏ i, p i (x i) := by
    intro x
    apply Finset.prod_nonneg
    intro i _
    exact hp_nonneg i (x i)
  have htail : (∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ), ∏ i, p i (x i))
      ≤ Real.exp (-(4 * t / V) * t)
        * (∑ x, (∏ i, p i (x i)) * Real.exp ((4 * t / V) * (f x - μ))) := by
    calc ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ), ∏ i, p i (x i)
        = ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ), (∏ i, p i (x i)) * 1 := by
          simp only [mul_one]
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ),
            (∏ i, p i (x i)) * Real.exp ((4 * t / V) * (f x - μ - t)) := by
          apply Finset.sum_le_sum
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have h1 : (1 : ℝ) ≤ Real.exp ((4 * t / V) * (f x - μ - t)) := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            apply mul_nonneg (le_of_lt hspos)
            linarith [hx]
          exact mul_le_mul_of_nonneg_left h1 (hw_nonneg x)
      _ = Real.exp (-(4 * t / V) * t) * ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ),
            (∏ i, p i (x i)) * Real.exp ((4 * t / V) * (f x - μ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          have hexp : (4 * t / V) * (f x - μ - t)
              = (4 * t / V) * (f x - μ) + (-(4 * t / V) * t) := by ring
          rw [hexp, Real.exp_add]
          ring
      _ ≤ Real.exp (-(4 * t / V) * t)
            * ∑ x, (∏ i, p i (x i)) * Real.exp ((4 * t / V) * (f x - μ)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro x _ _
            apply mul_nonneg (hw_nonneg x) (Real.exp_nonneg _)
  refine htail.trans ?_
  calc Real.exp (-(4 * t / V) * t)
          * (∑ x, (∏ i, p i (x i)) * Real.exp ((4 * t / V) * (f x - μ)))
      ≤ Real.exp (-(4 * t / V) * t) * Real.exp ((4 * t / V) ^ 2 * V / 8) := by
        apply mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)
    _ = Real.exp (-2 * t ^ 2 / V) := by
        rw [← Real.exp_add]
        congr 1
        have hVne : V ≠ 0 := ne_of_gt hc_pos
        field_simp
        ring


/-- Two-sided McDiarmid on a finite product space. -/
theorem mcdiarmid_product_two_sided {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    [∀ i, Nonempty (α i)]
    (p : ∀ i, α i → ℝ) (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a, p i a = 1)
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < ∑ i, c i ^ 2) (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : ∀ i, α i),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    (∑ x ∈ Finset.univ.filter
        (fun x => t ≤ |f x - ∑ y, (∏ i, p i (y i)) * f y|),
        ∏ i, p i (x i)) ≤ 2 * Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by

  classical
  set μ : ℝ := ∑ y, (∏ i, p i (y i)) * f y with hμ_def
  set V : ℝ := ∑ i, c i ^ 2 with hV_def
  have h1 := mcdiarmid_product p hp_nonneg hp_sum f c hc_nonneg hc_pos t ht hbd
  simp only [← hμ_def, ← hV_def] at h1
  have hbd_neg : ∀ (i : Fin n) (x y : ∀ i, α i),
      (∀ j, j ≠ i → x j = y j) → |(-f) x - (-f) y| ≤ c i := by
    intro i x y hxy
    have h := hbd i x y hxy
    have heq : (-f) x - (-f) y = -(f x - f y) := by simp [Pi.neg_apply]; ring
    rw [heq, abs_neg]
    exact h
  have h2 := mcdiarmid_product p hp_nonneg hp_sum (-f) c hc_nonneg hc_pos t ht hbd_neg
  have hμneg : (∑ y, (∏ i, p i (y i)) * (-f) y) = -μ := by
    have hneg : (∑ y, (∏ i, p i (y i)) * (-f) y)
        = -∑ y, (∏ i, p i (y i)) * f y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      simp [Pi.neg_apply]
    rw [hneg]
  -- fold h2's mean to -μ and V
  rw [hμneg] at h2
  simp only [← hV_def] at h2
  -- h2 : ∑ x ∈ filter (t ≤ (-f) x - -μ), w x ≤ exp (...)
  have hw_nonneg : ∀ x : (∀ i, α i), 0 ≤ ∏ i, p i (x i) := by
    intro x
    apply Finset.prod_nonneg
    intro i _
    exact hp_nonneg i (x i)
  -- subset: two-sided filter ⊆ one-sided f ∪ one-sided (-f)
  have hsub : Finset.univ.filter (fun x => t ≤ |f x - μ|)
      ⊆ Finset.univ.filter (fun x => t ≤ f x - μ)
        ∪ Finset.univ.filter (fun x => t ≤ (-f) x - -μ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    -- hx : t ≤ |f x - μ|
    by_cases hle : 0 ≤ f x - μ
    · left
      rw [abs_of_nonneg hle] at hx
      exact hx
    · right
      rw [abs_of_neg (lt_of_not_ge hle)] at hx
      -- hx : t ≤ -(f x - μ) = (-f) x - -μ
      have : (-f) x - -μ = -(f x - μ) := by simp [Pi.neg_apply]; ring
      rw [this]
      exact hx
  calc ∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x - μ|), ∏ i, p i (x i)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ)
          ∪ Finset.univ.filter (fun x => t ≤ (-f) x - -μ), ∏ i, p i (x i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro x _ _
        exact hw_nonneg x
    _ ≤ (∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ), ∏ i, p i (x i))
          + (∑ x ∈ Finset.univ.filter (fun x => t ≤ (-f) x - -μ), ∏ i, p i (x i)) := by
        have hunion := Finset.sum_union_inter
          (s₁ := Finset.univ.filter (fun x => t ≤ f x - μ))
          (s₂ := Finset.univ.filter (fun x => t ≤ (-f) x - -μ))
          (f := fun x => ∏ i, p i (x i))
        have hnonneg : 0 ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ f x - μ)
            ∩ Finset.univ.filter (fun x => t ≤ (-f) x - -μ), ∏ i, p i (x i) :=
          Finset.sum_nonneg (fun x _ => hw_nonneg x)
        linarith [hunion, hnonneg]
    _ ≤ Real.exp (-2 * t ^ 2 / V) + Real.exp (-2 * t ^ 2 / V) := by
        apply add_le_add h1 h2
    _ = 2 * Real.exp (-2 * t ^ 2 / V) := by ring
