/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingSymbol

namespace StatMech.FrontierA




def triangularIsingCriticalPolynomial (t r : ℝ) : ℝ :=
  1 + t ^ 2 * r - 2 * t - r - t ^ 2 - 2 * t * r



theorem triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq
    (x y : ℝ) :
    triangularIsingHighTempSymbol x x y 0 0 =
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 := by
  simp [triangularIsingHighTempSymbol, triangularIsingCriticalPolynomial]
  ring


theorem triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul
    (x y : ℝ) :
    triangularIsingSymbol x x y 0 0 =
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 *
        (Real.cosh x ^ 4 * Real.cosh y ^ 2) := by
  have h := triangularIsingHighTempSymbol_mul_cosh_sq x x y 0 0
  rw [triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq] at h
  calc
    triangularIsingSymbol x x y 0 0 =
        triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 *
          (Real.cosh x ^ 2 * Real.cosh x ^ 2 * Real.cosh y ^ 2) := h.symm
    _ = _ := by ring



theorem triangularIsingSymbol_zero_iff_criticalPolynomial_zero
    (x y : ℝ) :
    triangularIsingSymbol x x y 0 0 = 0 ↔
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) = 0 := by
  rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
  have hcosh : Real.cosh x ^ 4 * Real.cosh y ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Real.cosh_pos x).ne')
      (pow_ne_zero _ (Real.cosh_pos y).ne')
  rw [mul_eq_zero, or_iff_left hcosh, sq_eq_zero_iff]



theorem triangularIsingCriticalPolynomial_eq_zero_iff
    {t r : ℝ} (hden : 1 + 2 * t - t ^ 2 ≠ 0) :
    triangularIsingCriticalPolynomial t r = 0 ↔
      r = (1 - 2 * t - t ^ 2) / (1 + 2 * t - t ^ 2) := by
  unfold triangularIsingCriticalPolynomial
  constructor
  · intro h
    apply (eq_div_iff hden).2
    linarith
  · intro h
    apply (eq_div_iff hden).1 at h
    linarith



def triangularIsingCriticalCompanion (t r : ℝ) : ℝ :=
  1 + 2 * t - t ^ 2 + (1 - 2 * t - t ^ 2) * r

theorem triangularIsingCriticalCompanion_pos
    {t r : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hr0 : -1 < r) (hr1 : r < 1) :
    0 < triangularIsingCriticalCompanion t r := by
  unfold triangularIsingCriticalCompanion
  have htsq : t ^ 2 < 1 := by nlinarith [sq_nonneg (1 - t)]
  by_cases hA : 0 ≤ 1 - 2 * t - t ^ 2
  · have hm := mul_le_mul_of_nonneg_left (le_of_lt hr0) hA
    nlinarith
  · have hm := mul_lt_mul_of_neg_left hr1 (lt_of_not_ge hA)
    nlinarith


theorem sinh_two_mul_eq_two_tanh_div (x : ℝ) :
    Real.sinh (2 * x) =
      2 * Real.tanh x / (1 - Real.tanh x ^ 2) := by
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hcs := Real.cosh_sq_sub_sinh_sq x
  field_simp [hc]
  linear_combination Real.sinh x * hcs



noncomputable def triangularIsingCriticalRate (x y : ℝ) : ℝ :=
  Real.sinh (2 * x) ^ 2 +
    2 * Real.sinh (2 * x) * Real.sinh (2 * y)

theorem criticalRate_sub_one_factor
    {t r : ℝ} (ht : 1 - t ^ 2 ≠ 0) (hr : 1 - r ^ 2 ≠ 0) :
    (2 * t / (1 - t ^ 2)) ^ 2 +
          2 * (2 * t / (1 - t ^ 2)) * (2 * r / (1 - r ^ 2)) - 1 =
      -triangularIsingCriticalPolynomial t r *
          triangularIsingCriticalCompanion t r /
        ((1 - t ^ 2) ^ 2 * (1 - r ^ 2)) := by
  unfold triangularIsingCriticalPolynomial triangularIsingCriticalCompanion
  field_simp [ht, hr]
  ring



noncomputable def triangularIsingCriticalFactor (x y : ℝ) : ℝ :=
  -triangularIsingCriticalCompanion (Real.tanh x) (Real.tanh y) /
    ((1 - Real.tanh x ^ 2) ^ 2 * (1 - Real.tanh y ^ 2))

theorem triangularIsingCriticalRate_sub_one_eq_polynomial_mul_factor
    (x y : ℝ) :
    triangularIsingCriticalRate x y - 1 =
      triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) *
        triangularIsingCriticalFactor x y := by
  have hx : 0 < 1 - Real.tanh x ^ 2 := by
    nlinarith [Real.neg_one_lt_tanh x, Real.tanh_lt_one x]
  have hy : 0 < 1 - Real.tanh y ^ 2 := by
    nlinarith [Real.neg_one_lt_tanh y, Real.tanh_lt_one y]
  have h := criticalRate_sub_one_factor hx.ne' hy.ne'
  rw [← sinh_two_mul_eq_two_tanh_div x,
    ← sinh_two_mul_eq_two_tanh_div y] at h
  change triangularIsingCriticalRate x y - 1 = _ at h
  rw [h]
  unfold triangularIsingCriticalFactor
  ring

theorem triangularIsingCriticalFactor_neg
    {x y : ℝ} (hx : 0 < x) :
    triangularIsingCriticalFactor x y < 0 := by
  let t := Real.tanh x
  let r := Real.tanh y
  have ht0 : 0 < t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)
  have ht1 : t < 1 := Real.tanh_lt_one x
  have hr0 : -1 < r := Real.neg_one_lt_tanh y
  have hr1 : r < 1 := Real.tanh_lt_one y
  have hcomp : 0 < triangularIsingCriticalCompanion t r :=
    triangularIsingCriticalCompanion_pos ht0 ht1 hr0 hr1
  have htx : 0 < 1 - t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
  have hry : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 + r) (by linarith : 0 < 1 - r)]
  change -triangularIsingCriticalCompanion t r /
      ((1 - t ^ 2) ^ 2 * (1 - r ^ 2)) < 0
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hcomp)
    (mul_pos (sq_pos_of_pos htx) hry)




theorem triangularIsingCriticalPolynomial_zero_iff_rate_eq_one
    {x y : ℝ} (hx : 0 < x) :
    triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) = 0 ↔
      triangularIsingCriticalRate x y = 1 := by
  let t := Real.tanh x
  let r := Real.tanh y
  have ht0 : 0 < t := by
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)
  have ht1 : t < 1 := Real.tanh_lt_one x
  have hr0 : -1 < r := Real.neg_one_lt_tanh y
  have hr1 : r < 1 := Real.tanh_lt_one y
  have htDenPos : 0 < 1 - t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
  have hrDenPos : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 + r) (by linarith : 0 < 1 - r)]
  have hcomp : 0 < triangularIsingCriticalCompanion t r :=
    triangularIsingCriticalCompanion_pos ht0 ht1 hr0 hr1
  have hfactor := criticalRate_sub_one_factor htDenPos.ne' hrDenPos.ne'
  rw [← sinh_two_mul_eq_two_tanh_div x,
    ← sinh_two_mul_eq_two_tanh_div y] at hfactor
  change triangularIsingCriticalPolynomial t r = 0 ↔
    triangularIsingCriticalRate x y = 1
  rw [show triangularIsingCriticalRate x y =
      Real.sinh (2 * x) ^ 2 +
        2 * Real.sinh (2 * x) * Real.sinh (2 * y) by rfl]
  constructor
  · intro h
    rw [h] at hfactor
    simp only [neg_zero, zero_mul, zero_div] at hfactor
    linarith
  · intro h
    have hzero :
        -triangularIsingCriticalPolynomial t r *
            triangularIsingCriticalCompanion t r /
          ((1 - t ^ 2) ^ 2 * (1 - r ^ 2)) = 0 := by
      rw [← hfactor]
      linarith
    have hden : (1 - t ^ 2) ^ 2 * (1 - r ^ 2) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ htDenPos.ne') hrDenPos.ne'
    rw [div_eq_zero_iff] at hzero
    have hnum := hzero.resolve_right hden
    rw [mul_eq_zero] at hnum
    exact neg_eq_zero.mp (hnum.resolve_right hcomp.ne')



theorem triangularIsingSymbol_zero_iff_criticalRate_eq_one
    {x y : ℝ} (hx : 0 < x) :
    triangularIsingSymbol x x y 0 0 = 0 ↔
      triangularIsingCriticalRate x y = 1 :=
  (triangularIsingSymbol_zero_iff_criticalPolynomial_zero x y).trans
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hx)



theorem triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg
    {J : ℝ} (hJ : 0 ≤ J) :
    StrictMonoOn
      (fun β : ℝ => triangularIsingCriticalRate β (β * J)) (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hlt
  change 0 < β₁ at hβ₁
  change 0 < β₂ at hβ₂
  let s₁ := Real.sinh (2 * β₁)
  let s₂ := Real.sinh (2 * β₂)
  let r₁ := Real.sinh (2 * (β₁ * J))
  let r₂ := Real.sinh (2 * (β₂ * J))
  have hs₁ : 0 < s₁ := Real.sinh_pos_iff.mpr (by linarith)
  have hs₂ : 0 < s₂ := Real.sinh_pos_iff.mpr (by linarith)
  have hs : s₁ < s₂ := by
    dsimp [s₁, s₂]
    rw [Real.sinh_lt_sinh]
    linarith
  have hr₁ : 0 ≤ r₁ := Real.sinh_nonneg_iff.mpr (by
    exact mul_nonneg (by norm_num) (mul_nonneg hβ₁.le hJ))
  have hr : r₁ ≤ r₂ := by
    dsimp [r₁, r₂]
    rw [Real.sinh_le_sinh]
    have hbJ : β₁ * J ≤ β₂ * J :=
      mul_le_mul_of_nonneg_right hlt.le hJ
    linarith
  have hsq : s₁ ^ 2 < s₂ ^ 2 := by nlinarith
  have hprod : s₁ * r₁ ≤ s₂ * r₂ :=
    mul_le_mul hs.le hr hr₁ hs₂.le
  change s₁ ^ 2 + 2 * s₁ * r₁ < s₂ ^ 2 + 2 * s₂ * r₂
  linarith

theorem continuous_triangularIsingCriticalRateAlong (J : ℝ) :
    Continuous fun β : ℝ => triangularIsingCriticalRate β (β * J) := by
  unfold triangularIsingCriticalRate
  fun_prop



theorem existsUnique_triangularIsingCriticalRate_eq_one_of_nonneg
    {J : ℝ} (hJ : 0 ≤ J) :
    ∃! β : ℝ, 0 < β ∧ triangularIsingCriticalRate β (β * J) = 1 := by
  let f : ℝ → ℝ := fun β => triangularIsingCriticalRate β (β * J)
  have hf0 : f 0 = 0 := by simp [f, triangularIsingCriticalRate]
  have hsinh : 2 < Real.sinh 2 := by
    have h := Real.sinh_sub_id_strictMono (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
  have hrnonneg : 0 ≤ Real.sinh (2 * ((1 : ℝ) * J)) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hf1 : 1 < f 1 := by
    dsimp [f, triangularIsingCriticalRate]
    norm_num only [mul_one, one_mul]
    have hsquare : 4 < Real.sinh 2 ^ 2 := by nlinarith
    have hcross : 0 ≤ 2 * Real.sinh 2 * Real.sinh (2 * J) := by
      positivity
    linarith
  have honeMem : (1 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    rw [hf0]
    exact ⟨zero_le_one, hf1.le⟩
  obtain ⟨β, hβmem, hβeq⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      (continuous_triangularIsingCriticalRateAlong J).continuousOn honeMem
  change f β = 1 at hβeq
  have hβeq' : triangularIsingCriticalRate β (β * J) = 1 := hβeq
  have hβpos : 0 < β := by
    rcases hβmem with ⟨hβ0, -⟩
    refine hβ0.lt_of_ne ?_
    intro hβ
    subst β
    rw [hf0] at hβeq
    norm_num at hβeq
  refine ⟨β, ⟨hβpos, hβeq'⟩, ?_⟩
  intro γ hγ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg hJ
      hγ.1 hβpos hlt
    change triangularIsingCriticalRate γ (γ * J) <
      triangularIsingCriticalRate β (β * J) at this
    rw [hγ.2, hβeq'] at this
    exact (lt_irrefl 1 this)
  · have := triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg hJ
      hβpos hγ.1 hgt
    change triangularIsingCriticalRate β (β * J) <
      triangularIsingCriticalRate γ (γ * J) at this
    rw [hβeq', hγ.2] at this
    exact (lt_irrefl 1 this)



theorem existsUnique_triangularIsingSymbol_zero_of_nonneg
    {J : ℝ} (hJ : 0 ≤ J) :
    ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
  let h := existsUnique_triangularIsingCriticalRate_eq_one_of_nonneg hJ
  rcases h with ⟨β, hβ, huniq⟩
  refine ⟨β, ⟨hβ.1, ?_⟩, ?_⟩
  · exact (triangularIsingSymbol_zero_iff_criticalRate_eq_one hβ.1).2 hβ.2
  · intro γ hγ
    apply huniq γ
    exact ⟨hγ.1,
      (triangularIsingSymbol_zero_iff_criticalRate_eq_one hγ.1).1 hγ.2⟩



theorem sinh_scale_ratio_derivNumerator_pos
    {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    0 < Real.cosh x * Real.sinh (a * x) -
      a * Real.sinh x * Real.cosh (a * x) := by
  let H : ℝ → ℝ := fun z =>
    Real.cosh z * Real.sinh (a * z) -
      a * Real.sinh z * Real.cosh (a * z)
  have hcont : Continuous H := by
    dsimp [H]
    fun_prop
  have hmono : StrictMonoOn H (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
    intro z hz
    rw [interior_Ici, Set.mem_Ioi] at hz
    have hlin : HasDerivAt (fun w : ℝ => a * w) a z := by
      convert (hasDerivAt_id z).const_mul a using 1 <;> ring
    have hsinhA : HasDerivAt (fun w : ℝ => Real.sinh (a * w))
        (a * Real.cosh (a * z)) z := by
      convert (Real.hasDerivAt_sinh (a * z)).comp z hlin using 1 <;> ring
    have hcoshA : HasDerivAt (fun w : ℝ => Real.cosh (a * w))
        (a * Real.sinh (a * z)) z := by
      convert (Real.hasDerivAt_cosh (a * z)).comp z hlin using 1 <;> ring
    have hderiv : HasDerivAt H
        ((1 - a ^ 2) * Real.sinh z * Real.sinh (a * z)) z := by
      have h := (Real.hasDerivAt_cosh z).mul hsinhA |>.sub
        (((Real.hasDerivAt_sinh z).const_mul a).mul hcoshA)
      convert h using 1 <;> dsimp [H] <;> ring
    rw [hderiv.deriv]
    have haSq : a ^ 2 < 1 := by nlinarith [sq_nonneg (1 - a)]
    have hsx : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
    have hsa : 0 < Real.sinh (a * z) :=
      Real.sinh_pos_iff.mpr (mul_pos ha0 hz)
    positivity
  have hHx := hmono (by simp) (le_of_lt hx) hx
  simpa [H] using hHx



theorem sinh_scale_ratio_strictMonoOn
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (fun x : ℝ => Real.sinh x / Real.sinh (a * x))
      (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      rw [Real.sinh_ne_zero]
      exact mul_ne_zero ha0.ne' hx.ne'
  · intro x hx
    rw [interior_Ioi, Set.mem_Ioi] at hx
    have hlin : HasDerivAt (fun w : ℝ => a * w) a x := by
      convert (hasDerivAt_id x).const_mul a using 1 <;> ring
    have hsinhA : HasDerivAt (fun w : ℝ => Real.sinh (a * w))
        (a * Real.cosh (a * x)) x := by
      convert (Real.hasDerivAt_sinh (a * x)).comp x hlin using 1 <;> ring
    have hderiv : HasDerivAt
        (fun w : ℝ => Real.sinh w / Real.sinh (a * w))
        ((Real.cosh x * Real.sinh (a * x) -
          a * Real.sinh x * Real.cosh (a * x)) /
            Real.sinh (a * x) ^ 2) x := by
      have hne : Real.sinh (a * x) ≠ 0 :=
        Real.sinh_ne_zero.mpr (mul_ne_zero ha0.ne' hx.ne')
      convert (Real.hasDerivAt_sinh x).div hsinhA hne using 1 <;> ring
    rw [hderiv.deriv]
    exact div_pos (sinh_scale_ratio_derivNumerator_pos ha0 ha1 hx)
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos ha0 hx)))

private theorem triangularIsingCriticalRate_eq_one_lt_false_of_neg
    {J β₁ β₂ : ℝ} (hJlo : -1 < J) (hJhi : J < 0)
    (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβlt : β₁ < β₂)
    (hone₁ : triangularIsingCriticalRate β₁ (β₁ * J) = 1)
    (hone₂ : triangularIsingCriticalRate β₂ (β₂ * J) = 1) :
    False := by
  let a := -J
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  let x₁ := 2 * β₁
  let x₂ := 2 * β₂
  let s₁ := Real.sinh x₁
  let s₂ := Real.sinh x₂
  let q₁ := Real.sinh (a * x₁)
  let q₂ := Real.sinh (a * x₂)
  have hx₁ : 0 < x₁ := by dsimp [x₁]; linarith
  have hx₂ : 0 < x₂ := by dsimp [x₂]; linarith
  have hs₁ : 0 < s₁ := Real.sinh_pos_iff.mpr hx₁
  have hs₂ : 0 < s₂ := Real.sinh_pos_iff.mpr hx₂
  have hq₁ : 0 < q₁ := Real.sinh_pos_iff.mpr (mul_pos ha0 hx₁)
  have hq₂ : 0 < q₂ := Real.sinh_pos_iff.mpr (mul_pos ha0 hx₂)
  have hy₁ : 2 * (β₁ * J) = -(a * x₁) := by dsimp [a, x₁]; ring
  have hy₂ : 2 * (β₂ * J) = -(a * x₂) := by dsimp [a, x₂]; ring
  have hprod₁ : s₁ * (s₁ - 2 * q₁) = 1 := by
    rw [triangularIsingCriticalRate, hy₁, Real.sinh_neg] at hone₁
    change s₁ ^ 2 + 2 * s₁ * -q₁ = 1 at hone₁
    nlinarith
  have hprod₂ : s₂ * (s₂ - 2 * q₂) = 1 := by
    rw [triangularIsingCriticalRate, hy₂, Real.sinh_neg] at hone₂
    change s₂ ^ 2 + 2 * s₂ * -q₂ = 1 at hone₂
    nlinarith
  have hd₁ : 0 < s₁ - 2 * q₁ := by
    have hp : 0 < s₁ * (s₁ - 2 * q₁) := by rw [hprod₁]; norm_num
    rcases mul_pos_iff.mp hp with h | h
    · exact h.2
    · exact (lt_asymm hs₁ h.1).elim
  have hfactor₁ : s₁ ^ 2 * (1 - 2 * (q₁ / s₁)) = 1 := by
    calc
      s₁ ^ 2 * (1 - 2 * (q₁ / s₁)) = s₁ * (s₁ - 2 * q₁) := by
        field_simp [hs₁.ne']
      _ = 1 := hprod₁
  have hfactor₂ : s₂ ^ 2 * (1 - 2 * (q₂ / s₂)) = 1 := by
    calc
      s₂ ^ 2 * (1 - 2 * (q₂ / s₂)) = s₂ * (s₂ - 2 * q₂) := by
        field_simp [hs₂.ne']
      _ = 1 := hprod₂
  have hxlt : x₁ < x₂ := by dsimp [x₁, x₂]; linarith
  have hratio := sinh_scale_ratio_strictMonoOn ha0 ha1 hx₁ hx₂ hxlt
  change s₁ / q₁ < s₂ / q₂ at hratio
  have hcross : s₁ * q₂ < s₂ * q₁ :=
    (div_lt_div_iff₀ hq₁ hq₂).mp hratio
  have hreverse : q₂ / s₂ < q₁ / s₁ :=
    (div_lt_div_iff₀ hs₂ hs₁).2 (by nlinarith)
  have hp₁ : 0 < 1 - 2 * (q₁ / s₁) := by
    have := div_pos hd₁ hs₁
    convert this using 1 <;> field_simp [hs₁.ne'] <;> ring
  have hp : 1 - 2 * (q₁ / s₁) < 1 - 2 * (q₂ / s₂) := by linarith
  have hsq : s₁ ^ 2 < s₂ ^ 2 := by
    have hs : s₁ < s₂ := by
      dsimp [s₁, s₂]
      rw [Real.sinh_lt_sinh]
      exact hxlt
    nlinarith
  have hstep₁ : s₁ ^ 2 * (1 - 2 * (q₁ / s₁)) <
      s₂ ^ 2 * (1 - 2 * (q₁ / s₁)) :=
    mul_lt_mul_of_pos_right hsq hp₁
  have hstep₂ : s₂ ^ 2 * (1 - 2 * (q₁ / s₁)) <
      s₂ ^ 2 * (1 - 2 * (q₂ / s₂)) :=
    mul_lt_mul_of_pos_left hp (sq_pos_of_pos hs₂)
  linarith



theorem triangularIsingCriticalRate_eq_one_unique_of_neg
    {J β₁ β₂ : ℝ} (hJlo : -1 < J) (hJhi : J < 0)
    (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hone₁ : triangularIsingCriticalRate β₁ (β₁ * J) = 1)
    (hone₂ : triangularIsingCriticalRate β₂ (β₂ * J) = 1) :
    β₁ = β₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact triangularIsingCriticalRate_eq_one_lt_false_of_neg
      hJlo hJhi hβ₁ hβ₂ hlt hone₁ hone₂
  · exact triangularIsingCriticalRate_eq_one_lt_false_of_neg
      hJlo hJhi hβ₂ hβ₁ hgt hone₂ hone₁



theorem exists_triangularIsingCriticalRate_gt_one_of_neg
    {J : ℝ} (hJlo : -1 < J) (hJhi : J < 0) :
    ∃ β : ℝ, 0 < β ∧ 1 < triangularIsingCriticalRate β (β * J) := by
  let a := -J
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  let x := Real.log 8 / (1 - a)
  have hden : 0 < 1 - a := by linarith
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  have hscale : (1 - a) * x = Real.log 8 := by
    dsimp [x]
    field_simp [hden.ne']
  have hexpScale : Real.exp ((1 - a) * x) = 8 := by
    rw [hscale, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  have hsplit : x = (1 - a) * x + a * x := by ring
  have hexpX : Real.exp x = 8 * Real.exp (a * x) := by
    calc
      Real.exp x = Real.exp ((1 - a) * x + a * x) := congrArg Real.exp hsplit
      _ = Real.exp ((1 - a) * x) * Real.exp (a * x) := Real.exp_add _ _
      _ = 8 * Real.exp (a * x) := by rw [hexpScale]
  have hax : 0 < a * x := mul_pos ha0 hx
  have hE : 1 < Real.exp (a * x) := Real.one_lt_exp_iff.mpr hax
  have hExpX : 8 < Real.exp x := by rw [hexpX]; nlinarith
  have hExpNegX : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hsinhX : 3 < Real.sinh x := by
    rw [Real.sinh_eq]
    nlinarith
  have hneg : Real.exp (-x) < Real.exp (-(a * x)) := by
    rw [Real.exp_lt_exp]
    nlinarith
  have hinner : 3 < Real.sinh x - 2 * Real.sinh (a * x) := by
    rw [Real.sinh_eq, Real.sinh_eq, hexpX]
    nlinarith [Real.exp_pos (-(a * x))]
  let β := x / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨β, hβ, ?_⟩
  have htwo : 2 * β = x := by dsimp [β]; ring
  have hthird : 2 * (β * J) = -(a * x) := by
    dsimp [β, a]
    ring
  rw [triangularIsingCriticalRate, htwo, hthird, Real.sinh_neg]
  nlinarith [mul_pos (by linarith : 0 < Real.sinh x - 3)
    (by linarith : 0 < Real.sinh x - 2 * Real.sinh (a * x) - 3)]

theorem existsUnique_triangularIsingCriticalRate_eq_one_of_neg
    {J : ℝ} (hJlo : -1 < J) (hJhi : J < 0) :
    ∃! β : ℝ, 0 < β ∧ triangularIsingCriticalRate β (β * J) = 1 := by
  obtain ⟨B, hBpos, hB⟩ := exists_triangularIsingCriticalRate_gt_one_of_neg hJlo hJhi
  let f : ℝ → ℝ := fun β => triangularIsingCriticalRate β (β * J)
  have hf0 : f 0 = 0 := by simp [f, triangularIsingCriticalRate]
  have honeMem : (1 : ℝ) ∈ Set.Icc (f 0) (f B) := by
    rw [hf0]
    exact ⟨zero_le_one, hB.le⟩
  obtain ⟨β, hβmem, hβeq⟩ :=
    intermediate_value_Icc hBpos.le
      (continuous_triangularIsingCriticalRateAlong J).continuousOn honeMem
  change f β = 1 at hβeq
  have hβeq' : triangularIsingCriticalRate β (β * J) = 1 := hβeq
  have hβpos : 0 < β := by
    rcases hβmem with ⟨hβ0, -⟩
    refine hβ0.lt_of_ne ?_
    intro hzero
    subst β
    rw [hf0] at hβeq
    norm_num at hβeq
  refine ⟨β, ⟨hβpos, hβeq'⟩, ?_⟩
  intro γ hγ
  exact triangularIsingCriticalRate_eq_one_unique_of_neg
    hJlo hJhi hγ.1 hβpos hγ.2 hβeq'

theorem existsUnique_triangularIsingSymbol_zero_of_neg
    {J : ℝ} (hJlo : -1 < J) (hJhi : J < 0) :
    ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
  obtain ⟨β, hβ, huniq⟩ :=
    existsUnique_triangularIsingCriticalRate_eq_one_of_neg hJlo hJhi
  refine ⟨β, ⟨hβ.1,
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hβ.1).2 hβ.2⟩, ?_⟩
  intro γ hγ
  apply huniq γ
  exact ⟨hγ.1,
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hγ.1).1 hγ.2⟩



theorem existsUnique_triangularIsingSymbol_zero_of_gt_neg_one
    {J : ℝ} (hJ : -1 < J) :
    ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
  by_cases hnonneg : 0 ≤ J
  · exact existsUnique_triangularIsingSymbol_zero_of_nonneg hnonneg
  · exact existsUnique_triangularIsingSymbol_zero_of_neg hJ (lt_of_not_ge hnonneg)


noncomputable def triangularIsingCriticalRateAlongDeriv (β J : ℝ) : ℝ :=
  4 * Real.sinh (2 * β) * Real.cosh (2 * β) +
    4 * Real.cosh (2 * β) * Real.sinh (2 * (β * J)) +
    4 * J * Real.sinh (2 * β) * Real.cosh (2 * (β * J))

theorem hasDerivAt_triangularIsingCriticalRateAlong (β J : ℝ) :
    HasDerivAt (fun b : ℝ => triangularIsingCriticalRate b (b * J))
      (triangularIsingCriticalRateAlongDeriv β J) β := by
  have hx : HasDerivAt (fun b : ℝ => 2 * b) 2 β := by
    convert (hasDerivAt_id β).const_mul 2 using 1 <;> ring
  have hy : HasDerivAt (fun b : ℝ => 2 * (b * J)) (2 * J) β := by
    convert ((hasDerivAt_id β).mul_const J).const_mul 2 using 1 <;> ring
  have hs : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * β)) β := by
    convert (Real.hasDerivAt_sinh (2 * β)).comp β hx using 1 <;> ring
  have hr : HasDerivAt (fun b : ℝ => Real.sinh (2 * (b * J)))
      (2 * J * Real.cosh (2 * (β * J))) β := by
    convert (Real.hasDerivAt_sinh (2 * (β * J))).comp β hy using 1 <;> ring
  have h := (hs.pow 2).add ((hs.mul hr).const_mul 2)
  convert h using 1
  · ext b
    simp only [triangularIsingCriticalRate, Pi.pow_apply, Pi.add_apply,
      Pi.mul_apply]
    ring
  · simp only [triangularIsingCriticalRateAlongDeriv]
    ring


theorem triangularIsingCriticalRateAlongDeriv_pos_at_root
    {β J : ℝ} (hβ : 0 < β) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    0 < triangularIsingCriticalRateAlongDeriv β J := by
  by_cases hnonneg : 0 ≤ J
  · have hs : 0 < Real.sinh (2 * β) := Real.sinh_pos_iff.mpr (by linarith)
    have hr : 0 ≤ Real.sinh (2 * (β * J)) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    have hc : 0 < Real.cosh (2 * β) := Real.cosh_pos _
    have hcr : 0 < Real.cosh (2 * (β * J)) := Real.cosh_pos _
    unfold triangularIsingCriticalRateAlongDeriv
    positivity
  · have hJneg : J < 0 := lt_of_not_ge hnonneg
    let a := -J
    let x := 2 * β
    let s := Real.sinh x
    let q := Real.sinh (a * x)
    have ha0 : 0 < a := by dsimp [a]; linarith
    have ha1 : a < 1 := by dsimp [a]; linarith
    have hx : 0 < x := by dsimp [x]; linarith
    have hs : 0 < s := Real.sinh_pos_iff.mpr hx
    have hy : 2 * (β * J) = -(a * x) := by dsimp [a, x]; ring
    have hprod : s * (s - 2 * q) = 1 := by
      rw [triangularIsingCriticalRate, hy, Real.sinh_neg] at hroot
      change s ^ 2 + 2 * s * -q = 1 at hroot
      nlinarith
    have hd : 0 < s - 2 * q := by
      have hp : 0 < s * (s - 2 * q) := by rw [hprod]; norm_num
      rcases mul_pos_iff.mp hp with h | h
      · exact h.2
      · exact (lt_asymm hs h.1).elim
    have hnum : 0 < Real.cosh x * q -
        a * s * Real.cosh (a * x) := by
      exact sinh_scale_ratio_derivNumerator_pos ha0 ha1 hx
    have hmain : 0 < Real.cosh x * (s - 2 * q) :=
      mul_pos (Real.cosh_pos x) hd
    rw [triangularIsingCriticalRateAlongDeriv, show 2 * β = x by rfl,
      hy, Real.sinh_neg, Real.cosh_neg]
    change 0 < 4 * s * Real.cosh x + 4 * Real.cosh x * -q +
      4 * J * s * Real.cosh (a * x)
    dsimp [a] at hnum
    nlinarith

end StatMech.FrontierA
