/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.LorentzianPolynomials
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bivariate Lorentzian polynomials

A bivariate form is Lorentzian precisely when its coefficients are nonnegative,
ultra log-concave and have no internal zeros.
-/

public section

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted

open Finsupp MvPolynomial UpperHalfPlane
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials

private noncomputable def powers (d k : ℕ) : Fin 2 →₀ ℕ := single 0 k + single 1 (d - k)

private lemma powers_zero (d k : ℕ) : powers d k 0 = k := by simp [powers]

private lemma powers_one (d k : ℕ) : powers d k 1 = d - k := by simp [powers]

private lemma powers_ext {m : Fin 2 →₀ ℕ} {d : ℕ} (hm : m 0 + m 1 = d) :
    powers d (m 0) = m := by
  ext i
  fin_cases i <;> simp [powers]
  omega

private noncomputable def rawCoeff {d : ℕ} (f : H 2 d) (k : ℕ) : ℝ := f.1.coeff (powers d k)

private noncomputable def normalizedCoeff {d : ℕ} (f : H 2 d) (k : ℕ) : ℝ :=
  rawCoeff f k / d.choose k

private lemma choose_pos {d k : ℕ} (hk : k ≤ d) : (0 : ℝ) < d.choose k := by
  exact_mod_cast Nat.choose_pos hk

private lemma normalized_nonneg {d k : ℕ} (f : H 2 d) (hk : k ≤ d) :
    0 ≤ normalizedCoeff f k ↔ 0 ≤ rawCoeff f k := by
  simp [normalizedCoeff, le_div_iff₀ (choose_pos hk)]

private lemma normalized_pos {d k : ℕ} (f : H 2 d) (hk : k ≤ d) :
    0 < normalizedCoeff f k ↔ 0 < rawCoeff f k := div_pos_iff_of_pos_right (choose_pos hk)

private lemma support_degree {d : ℕ} (f : H 2 d) {m} (hm : m ∈ f.1.support) :
    m 0 + m 1 = d := by
  have hd := f.2 (MvPolynomial.mem_support_iff.mp hm)
  simpa only [Pi.one_def, ← degree_eq_weight_one, degree_eq_sum, Fin.sum_univ_two] using hd

private lemma all_nonneg {d : ℕ} (f : H 2 d) :
    (∀ m, 0 ≤ f.1.coeff m) ↔ ∀ k ≤ d, 0 ≤ normalizedCoeff f k := by
  constructor
  · exact fun h k hk => (normalized_nonneg f hk).2 (h _)
  · intro h m
    by_cases hm : m ∈ f.1.support
    · have hd := support_degree f hm
      simpa only [rawCoeff, powers_ext hd] using
        (normalized_nonneg f (k := m 0) (by omega)).1 (h _ (by omega))
    · simp [MvPolynomial.notMem_support_iff.mp hm]

private def NoGaps (d : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → k ≤ d → 0 < c i → 0 < c k → 0 < c j

private def LogConcave (d : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ k, k + 2 ≤ d → c k * c (k + 2) ≤ c (k + 1) ^ 2

private def CoeffConditions (d : ℕ) (c : ℕ → ℝ) : Prop :=
  (∀ k ≤ d, 0 ≤ c k) ∧ LogConcave d c ∧ NoGaps d c

private lemma shift_up {d i : ℕ} :
    powers d i - single 1 1 + single 0 1 = powers d (i + 1) := by
  ext j
  fin_cases j <;> simp [powers]
  omega

private lemma shift_down {d i : ℕ} (hi : 0 < i) (hid : i ≤ d) :
    powers d i - single 0 1 + single 1 1 = powers d (i - 1) := by
  ext j
  fin_cases j <;> simp [powers]
  omega

private lemma convex_iff_noGaps {d : ℕ} (f : H 2 d) (hn : ∀ m, 0 ≤ f.1.coeff m) :
    IsMConvex (f.1.support : Set (Fin 2 →₀ ℕ)) ↔ NoGaps d (normalizedCoeff f) := by
  have mem (k : ℕ) (hk : k ≤ d) : powers d k ∈ f.1.support ↔ 0 < normalizedCoeff f k := by
    rw [normalized_pos f hk, MvPolynomial.mem_support_iff]
    exact (hn _).lt_iff_ne'.symm
  constructor
  · intro hc i j k hij hjk hkd hi hk
    induction j, hij using Nat.le_induction with
    | base => exact hi
    | succ j _ ih =>
      have hj := (mem j (by omega)).2 (ih (by omega))
      obtain ⟨t, ht, he⟩ := hc _ hj _ ((mem k hkd).2 hk) 1
        (by simp only [powers_one]; omega)
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · exact (mem _ (by omega)).1 ((shift_up (d := d) (i := j)) ▸ he)
      · simp only [powers_one] at ht
        omega
  · intro hg m hm n hn' t ht
    have hmd := support_degree f hm
    have hnd := support_degree f hn'
    have hm' := (mem (m 0) (by omega)).1 ((powers_ext hmd).symm ▸ hm)
    have hn'' := (mem (n 0) (by omega)).1 ((powers_ext hnd).symm ▸ hn')
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · refine ⟨1, by omega, ?_⟩
      rw [← powers_ext hmd, shift_down (d := d) (i := m 0) (by omega) (by omega)]
      exact (mem _ (by omega)).2 (hg _ _ _ (by omega) (by omega) (by omega) hn'' hm')
    · refine ⟨0, by omega, ?_⟩
      rw [← powers_ext hmd, shift_up]
      exact (mem _ (by omega)).2 (hg _ _ _ (by omega) (by omega) (by omega) hm' hn'')

private noncomputable abbrev partialForm {d : ℕ} (f : H 2 (d + 1)) (t : Fin 2) : H 2 d :=
  ⟨pderiv t f.1, f.2.pderiv⟩

-- Binomial normalization turns the two partial derivatives into a shifted and an
-- unshifted copy of the coefficient sequence, with the same positive scale factor.
private lemma normalized_partial_zero {d k : ℕ} (f : H 2 (d + 1)) (hk : k ≤ d) :
    normalizedCoeff (partialForm f 0) k = (d + 1 : ℕ) * normalizedCoeff f (k + 1) := by
  have he : powers d k + single 0 1 = powers (d + 1) (k + 1) := by
    ext t
    fin_cases t <;> simp [powers]
  have hc : ((d + 1 : ℕ) : ℝ) * d.choose k = (d + 1).choose (k + 1) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq d k
  have h₁ := (choose_pos hk).ne'
  have h₂ := (choose_pos (Nat.succ_le_succ hk)).ne'
  simp only [normalizedCoeff, rawCoeff, coeff_pderiv, he, powers_zero]
  field_simp
  linear_combination (f.1.coeff (powers (d + 1) (k + 1))) * (-hc)

private lemma normalized_partial_one {d k : ℕ} (f : H 2 (d + 1)) (hk : k ≤ d) :
    normalizedCoeff (partialForm f 1) k = (d + 1 : ℕ) * normalizedCoeff f k := by
  have he : powers d k + single 1 1 = powers (d + 1) k := by
    ext t
    fin_cases t <;> simp [powers]
    omega
  have hc : (d.choose k : ℝ) * (d + 1 : ℕ) = (d + 1).choose k * ((d + 1 - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq d k
  have h₁ := (choose_pos hk).ne'
  have h₂ := (choose_pos (Nat.le_succ_of_le hk)).ne'
  have hs : ((d - k : ℕ) : ℝ) + 1 = (d + 1 - k : ℕ) := by
    exact_mod_cast (show d - k + 1 = d + 1 - k by omega)
  simp only [normalizedCoeff, rawCoeff, coeff_pderiv, he, powers_one, hs]
  field_simp
  linear_combination (f.1.coeff (powers (d + 1) k)) * (-hc)

private lemma coeffConditions_slice {d s : ℕ} {c v : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hs : s ≤ 1) (hv : ∀ k ≤ d, v k = r * c (k + s)) (h : CoeffConditions (d + 1) c) :
    CoeffConditions d v := by
  refine ⟨fun k hk => (hv k hk).symm ▸ mul_nonneg hr.le (h.1 _ (by omega)), ?_, ?_⟩
  · intro k hk
    rw [hv _ (by omega), hv _ hk, hv _ (by omega), mul_pow, mul_mul_mul_comm, sq r]
    apply mul_le_mul_of_nonneg_left _ (mul_self_nonneg r)
    simpa only [Nat.add_right_comm k] using h.2.1 (k + s) (by omega)
  · intro i j k hij hjk hkd hi hk
    rw [hv _ (by omega), mul_pos_iff_of_pos_left hr] at hi ⊢
    rw [hv _ hkd, mul_pos_iff_of_pos_left hr] at hk
    exact h.2.2 _ _ _ (by omega) (by omega) (by omega) hi hk

private lemma logConcave_of_slice {d s : ℕ} {c v : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ∀ k ≤ d, v k = r * c (k + s)) (h : LogConcave d v) (k : ℕ) (hk : k + 2 ≤ d) :
    c (k + s) * c (k + s + 2) ≤ c (k + s + 1) ^ 2 := by
  have hh := h k hk
  rw [hv _ (by omega), hv _ hk, hv _ (by omega), mul_pow, mul_mul_mul_comm, sq r] at hh
  simpa only [Nat.add_right_comm k] using (le_of_mul_le_mul_left hh (mul_self_pos.mpr hr.ne'))

private lemma mem_iff_coeffConditions_step (d : ℕ)
    (ih : ∀ g : H 2 (d + 2), g ∈ L 2 (d + 2) ↔ CoeffConditions (d + 2) (normalizedCoeff g))
    (f : H 2 (d + 3)) :
    f ∈ L 2 (d + 3) ↔ CoeffConditions (d + 3) (normalizedCoeff f) := by
  change (f ∈ M 2 (d + 3) ∧ ∀ t, partialForm f t ∈ L 2 (d + 2)) ↔ _
  have h₀ (k : ℕ) (hk : k ≤ d + 2) := normalized_partial_zero f hk
  have h₁ (k : ℕ) (hk : k ≤ d + 2) :
      normalizedCoeff (partialForm f 1) k = (d + 3 : ℕ) * normalizedCoeff f (k + 0) :=
    normalized_partial_one f hk
  have hr : (0 : ℝ) < (d + 3 : ℕ) := by positivity
  constructor
  · rintro ⟨⟨hc, hn⟩, hD⟩
    refine ⟨(all_nonneg f).1 hn, ?_, (convex_iff_noGaps f hn).1 hc⟩
    intro k hk
    cases k with
    | zero => exact logConcave_of_slice hr h₁ ((ih _).1 (hD 1)).2.1 0 (by omega)
    | succ k => exact logConcave_of_slice hr h₀ ((ih _).1 (hD 0)).2.1 k (by omega)
  · intro h
    have hn := (all_nonneg f).2 h.1
    refine ⟨⟨(convex_iff_noGaps f hn).2 h.2.2, hn⟩, ?_⟩
    intro t
    apply (ih _).2
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · exact coeffConditions_slice hr (by decide) h₀ h
    · exact coeffConditions_slice hr (by decide) h₁ h

private lemma expansion {d : ℕ} (f : H 2 d) :
    f.1 = ∑ k ∈ Finset.range (d + 1), monomial (powers d k) (rawCoeff f k) := by
  classical
  let s := (Finset.range (d + 1)).image (powers d)
  have hs : f.1.support ⊆ s := by
    intro m hm
    have hd := support_degree f hm
    exact Finset.mem_image.mpr ⟨m 0, Finset.mem_range.mpr (by omega), powers_ext hd⟩
  calc
    _ = _ := f.1.as_sum
    _ = ∑ m ∈ s, monomial m (f.1.coeff m) := Finset.sum_subset hs (by
      intro m _ hm
      simp [MvPolynomial.notMem_support_iff.mp hm])
    _ = _ := Finset.sum_image (fun i _ j _ hij => by
      simpa only [powers_zero] using congrArg (fun m : Fin 2 →₀ ℕ => m 0) hij)

private lemma eval_expansion {d : ℕ} (f : H 2 d) (z : Fin 2 → ℍ) :
    aeval (((↑) : ℍ → ℂ) ∘ z) f.1 =
      ∑ k ∈ Finset.range (d + 1), (rawCoeff f k : ℂ) * (z 0 : ℂ) ^ k * (z 1 : ℂ) ^ (d - k) := by
  conv_lhs => rw [expansion f, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [powers_zero, powers_one, mul_assoc]

private lemma linear_ne_zero {x y : ℍ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : 0 < u ∨ 0 < v) : (u : ℂ) * x + (v : ℂ) * y ≠ 0 := by
  apply ne_of_apply_ne Complex.im
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im]
  rcases h with h | h
  · exact (add_pos_of_pos_of_nonneg (mul_pos h x.im_pos) (mul_nonneg hv y.im_pos.le)).ne'
  · exact (add_pos_of_nonneg_of_pos (mul_nonneg hu x.im_pos.le) (mul_pos h y.im_pos)).ne'

private lemma stable_zero_degree (f : H 2 0) : IsStable f.1 := by
  by_cases ha : rawCoeff f 0 = 0
  · left
    simp [expansion f, ha]
  · right
    intro z
    simpa [eval_expansion, Finset.sum_range_succ] using
      (show (rawCoeff f 0 : ℂ) ≠ 0 by exact_mod_cast ha)

private lemma stable_one_degree (f : H 2 1) (hn : ∀ k ≤ 1, 0 ≤ normalizedCoeff f k) :
    IsStable f.1 := by
  have h₀ := (normalized_nonneg f (by decide : 0 ≤ 1)).1 (hn 0 (by decide))
  have h₁ := (normalized_nonneg f (by decide : 1 ≤ 1)).1 (hn 1 (by decide))
  by_cases hp : 0 < rawCoeff f 0 ∨ 0 < rawCoeff f 1
  · right
    intro z
    rw [eval_expansion]
    simpa [Finset.sum_range_succ] using linear_ne_zero (x := z 1) (y := z 0) h₀ h₁ hp
  · push Not at hp
    left
    rw [expansion f]
    simp [Finset.sum_range_succ, le_antisymm hp.1 h₀, le_antisymm hp.2 h₁]

private lemma eval_two (f : H 2 2) (z : Fin 2 → ℍ) :
    aeval (((↑) : ℍ → ℂ) ∘ z) f.1 =
      (rawCoeff f 0 : ℂ) * (z 1 : ℂ) ^ 2 + (rawCoeff f 1 : ℂ) * z 0 * z 1 +
        (rawCoeff f 2 : ℂ) * (z 0 : ℂ) ^ 2 := by
  rw [eval_expansion]
  simp [Finset.sum_range_succ]

-- A negative discriminant produces a zero in the product of upper half-planes.
-- If s² = 4uw - v², take x = (-v + is)t and y = 2wt with t = v + 1 + is.
private lemma quadratic_discriminant {u v w : ℝ} (hw : 0 < w)
    (h : ∀ x y : ℍ, (u : ℂ) * (y : ℂ) ^ 2 + (v : ℂ) * x * y + (w : ℂ) * (x : ℂ) ^ 2 ≠ 0) :
    4 * u * w ≤ v ^ 2 := by
  by_contra! hneg
  let s := Real.sqrt (4 * u * w - v ^ 2)
  have hs : 0 < s := Real.sqrt_pos.2 (sub_pos.2 hneg)
  have hs₂ : s ^ 2 = 4 * u * w - v ^ 2 := Real.sq_sqrt (sub_nonneg.2 hneg.le)
  let r : ℂ := ⟨-v, s⟩
  let t : ℂ := ⟨v + 1, s⟩
  have hx : 0 < (r * t).im := by
    simp only [r, t, Complex.mul_im]
    linarith
  have hy : 0 < ((2 * (w : ℂ)) * t).im := by
    simpa [t, Complex.mul_im] using mul_pos (mul_pos zero_lt_two hw) hs
  have hr : r ^ 2 + 2 * (v : ℂ) * r + 4 * (u : ℂ) * w = 0 := by
    apply Complex.ext <;> simp [r, sq, Complex.mul_re, Complex.mul_im] <;> nlinarith
  apply h ⟨_, hx⟩ ⟨_, hy⟩
  change (u : ℂ) * (2 * w * t) ^ 2 + v * (r * t) * (2 * w * t) + w * (r * t) ^ 2 = 0
  linear_combination (w : ℂ) * t ^ 2 * hr

-- For nonnegative discriminant the two real linear factors have nonnegative
-- coefficients and a positive coefficient of x, so neither can vanish.
private lemma quadratic_ne_zero {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 < w)
    (hd : 4 * u * w ≤ v ^ 2) (x y : ℍ) :
    (u : ℂ) * (y : ℂ) ^ 2 + (v : ℂ) * x * y + (w : ℂ) * (x : ℂ) ^ 2 ≠ 0 := by
  let s := Real.sqrt (v ^ 2 - 4 * u * w)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs₂ : s ^ 2 = v ^ 2 - 4 * u * w := Real.sq_sqrt (sub_nonneg.2 hd)
  have hsv : s ≤ v := by nlinarith [mul_nonneg hu hw.le, sq_nonneg (s - v)]
  have hf (c : ℝ) (hc : 0 ≤ c) := linear_ne_zero (x := x) (y := y) (u := 2 * w)
    (v := c) (by positivity) hc (Or.inl (by positivity))
  have hprod := mul_ne_zero (hf (v + s) (add_nonneg hv hs)) (hf (v - s) (sub_nonneg.2 hsv))
  intro hz
  apply hprod
  have hsℂ : (s : ℂ) ^ 2 = (v : ℂ) ^ 2 - 4 * u * w := by exact_mod_cast hs₂
  push_cast
  linear_combination 4 * (w : ℂ) * hz - (y : ℂ) ^ 2 * hsℂ

private lemma stable_two_iff (f : H 2 2) (hn : ∀ k ≤ 2, 0 ≤ normalizedCoeff f k) :
    IsStable f.1 ↔ 4 * rawCoeff f 0 * rawCoeff f 2 ≤ rawCoeff f 1 ^ 2 := by
  have ha (k : ℕ) (hk : k ≤ 2) := (normalized_nonneg f hk).1 (hn k hk)
  by_cases hw : 0 < rawCoeff f 2
  · constructor
    · rintro (hz | h)
      · have : rawCoeff f 2 = 0 := by simp [rawCoeff, hz]
        linarith
      · apply quadratic_discriminant hw
        intro x y
        simpa [eval_two] using h ![x, y]
    · intro hd
      right
      intro z
      exact eval_two f z ▸ quadratic_ne_zero (ha 0 (by decide)) (ha 1 (by decide)) hw hd _ _
  · have hw' := le_antisymm (le_of_not_gt hw) (ha 2 (by decide))
    constructor
    · simp [hw', sq_nonneg]
    · intro _
      by_cases hp : 0 < rawCoeff f 0 ∨ 0 < rawCoeff f 1
      · right
        intro z
        have h := linear_ne_zero (x := z 1) (y := z 0) (ha 0 (by decide)) (ha 1 (by decide)) hp
        rw [eval_two, hw']
        simpa [add_mul, sq, mul_assoc] using mul_ne_zero h (z 1).ne_zero
      · push Not at hp
        left
        rw [expansion f]
        simp [Finset.sum_range_succ, hw', le_antisymm hp.1 (ha 0 (by decide)),
          le_antisymm hp.2 (ha 1 (by decide))]

private lemma coeffConditions_two_iff (f : H 2 2) :
    CoeffConditions 2 (normalizedCoeff f) ↔
      (∀ k ≤ 2, 0 ≤ normalizedCoeff f k) ∧ 4 * rawCoeff f 0 * rawCoeff f 2 ≤ rawCoeff f 1 ^ 2 := by
  have h₀ : normalizedCoeff f 0 = rawCoeff f 0 := by simp [normalizedCoeff]
  have h₁ : normalizedCoeff f 1 = rawCoeff f 1 / 2 := by norm_num [normalizedCoeff]
  have h₂ : normalizedCoeff f 2 = rawCoeff f 2 := by simp [normalizedCoeff]
  constructor
  · rintro ⟨hn, hc, -⟩
    have h := hc 0 (by decide)
    simp only [zero_add, h₀, h₁, h₂] at h
    exact ⟨hn, by linarith⟩
  · rintro ⟨hn, hd⟩
    refine ⟨hn, ?_, ?_⟩
    · intro k hk
      obtain rfl : k = 0 := by omega
      simp only [zero_add, h₀, h₁, h₂]
      linarith
    · intro i j k hij hjk hkd hi hk
      obtain rfl | hij := hij.eq_or_lt
      · exact hi
      obtain rfl | hjk := hjk.eq_or_lt
      · exact hk
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 1 := by omega
      obtain rfl : k = 2 := by omega
      rw [h₀] at hi
      rw [h₂] at hk
      have hnn := (normalized_nonneg f (by decide : 1 ≤ 2)).1 (hn 1 (by decide))
      rw [h₁]
      apply div_pos _ zero_lt_two
      nlinarith [mul_pos hi hk]

private lemma mem_iff_coeffConditions {d : ℕ} (f : H 2 d) :
    f ∈ L 2 d ↔ CoeffConditions d (normalizedCoeff f) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    match d with
    | 0 | 1 =>
      change (IsStable f.1 ∧ ∀ m, 0 ≤ f.1.coeff m) ↔ _
      rw [all_nonneg]
      constructor
      · rintro ⟨-, hn⟩
        refine ⟨hn, fun k hk => by omega, ?_⟩
        intro i j k hij hjk hkd hi hk
        rcases (show i = j ∨ k = j by omega) with rfl | rfl
        · exact hi
        · exact hk
      · intro h
        exact ⟨by first | exact stable_zero_degree f | exact stable_one_degree f h.1, h.1⟩
    | 2 =>
      change (IsStable f.1 ∧ ∀ m, 0 ≤ f.1.coeff m) ↔ _
      rw [all_nonneg, coeffConditions_two_iff, and_comm]
      exact and_congr_right (stable_two_iff f)
    | d + 3 => exact mem_iff_coeffConditions_step d (fun g => ih _ (by omega) g) f

/-- **Bivariate Lorentzian polynomials** (Brändén and Huh, *Lorentzian polynomials*, Ann. of
Math. 192 (2020), Example 2.26, with Example 2.3 and Theorem 2.25). Write a bivariate form of
degree `d` as `f = ∑_{k=0}^{d} a_k w_1^k w_2^{d-k}`. Then `f` is Lorentzian if and only if the
sequence `a_0, …, a_d` is nonnegative, ultra log-concave
(`a_k^2 / C(d,k)^2 ≥ a_{k-1} a_{k+1} / (C(d,k-1) C(d,k+1))` for `0 < k < d`), and has no internal
zeros (`a_{k_1} a_{k_3} > 0` implies `a_{k_2} > 0` for `k_1 < k_2 < k_3 ≤ d`). Here `w_1` is the
variable `0 : Fin 2` and `w_2` the variable `1 : Fin 2`. -/
theorem bivariate_mem_L_iff {d : ℕ} (f : H 2 d) :
    let a : ℕ → ℝ := fun k => f.1.coeff (single 0 k + single 1 (d - k))
    f ∈ L 2 d ↔
      (∀ k ≤ d, 0 ≤ a k) ∧
      (∀ k, 0 < k → k < d →
        a (k - 1) * a (k + 1) / ((d.choose (k - 1) : ℝ) * (d.choose (k + 1) : ℝ)) ≤
          a k ^ 2 / (d.choose k : ℝ) ^ 2) ∧
      (∀ k₁ k₂ k₃, k₁ < k₂ → k₂ < k₃ → k₃ ≤ d → 0 < a k₁ * a k₃ → 0 < a k₂) := by
  dsimp only
  rw [mem_iff_coeffConditions]
  constructor
  · rintro ⟨hn, hc, hg⟩
    refine ⟨fun k hk => (normalized_nonneg f hk).1 (hn k hk), ?_, ?_⟩
    · intro k hk hkd
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simpa only [Nat.succ_sub_one, normalizedCoeff, rawCoeff, powers,
        div_mul_div_comm, div_pow] using hc j (by omega)
    · intro i j k hij hjk hkd hp
      have hi := (normalized_nonneg f (by omega : i ≤ d)).1 (hn _ (by omega))
      have hk := (normalized_nonneg f hkd).1 (hn _ hkd)
      exact (normalized_pos f (by omega)).1 (hg i j k hij.le hjk.le hkd
        ((normalized_pos f (by omega)).2 (pos_of_mul_pos_left hp hk))
        ((normalized_pos f hkd).2 (pos_of_mul_pos_right hp hi)))
  · rintro ⟨hn, hc, hg⟩
    refine ⟨fun k hk => (normalized_nonneg f hk).2 (hn k hk), ?_, ?_⟩
    · intro k hk
      simpa only [Nat.add_one_sub_one, normalizedCoeff, rawCoeff, powers,
        div_mul_div_comm, div_pow] using
        hc (k + 1) (by omega) (by omega)
    · intro i j k hij hjk hkd hi hk
      obtain rfl | hij := hij.eq_or_lt
      · exact hi
      obtain rfl | hjk := hjk.eq_or_lt
      · exact hk
      apply (normalized_pos f (by omega)).2
      exact hg i j k hij hjk hkd (mul_pos
        ((normalized_pos f (by omega)).1 hi) ((normalized_pos f hkd).1 hk))

end MathlibExt.Combinatorics.LorentzianToolboxWanted
