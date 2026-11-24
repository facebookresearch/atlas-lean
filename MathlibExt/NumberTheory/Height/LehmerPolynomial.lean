/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.LehmerConstant
import Mathlib.Tactic.ComputeDegree

/-!
# Mahler measure of Lehmer's polynomial

We prove the upper bound `1.176281` by isolating the five real roots of the trace polynomial
obtained from Lehmer's reciprocal polynomial by the substitution `y = x + x⁻¹`.
-/

public section

namespace MathlibExt.NumberTheory.LehmerConstant

open Polynomial ComplexConjugate

private noncomputable def tracePoly : ℝ[X] :=
  X ^ 5 + X ^ 4 - 5 * X ^ 3 - 5 * X ^ 2 + 4 * X + 3

private noncomputable def quadratic (t : ℝ) : ℂ[X] :=
  X ^ 2 - C (t : ℂ) * X + 1

private lemma quadratic_factor {t : ℝ} {z w : ℂ} (hs : z + w = t) (hp : z * w = 1) :
    quadratic t = (X - C z) * (X - C w) := by
  have hsum := congrArg (C : ℂ → ℂ[X]) hs
  have hprod := congrArg (C : ℂ → ℂ[X]) hp
  simp only [map_add, map_mul, map_one] at hsum hprod
  unfold quadratic
  linear_combination X * hsum - hprod

private lemma quadratic_mahlerMeasure_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-2) 2) :
    (quadratic t).mahlerMeasure = 1 := by
  let z : ℂ := ⟨t / 2, Real.sqrt (1 - (t / 2) ^ 2)⟩
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply, ← sq, ← sq]
    dsimp [z]
    rw [Real.sq_sqrt]
    · ring
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ht.1)]
  have hn : ‖z‖ = 1 := by nlinarith [Complex.sq_norm z, norm_nonneg z]
  have hs : z + conj z = (t : ℂ) := by
    rw [Complex.add_conj]
    congr 1
    dsimp [z]
    ring
  have hp : z * conj z = 1 := by simp [Complex.mul_conj, hsq]
  simp [quadratic_factor hs hp, mahlerMeasure_mul, mahlerMeasure_X_sub_C, hn]

private lemma quadratic_mahlerMeasure_of_one_lt {r : ℝ} (hr : 1 < r) :
    (quadratic (r + r⁻¹)).mahlerMeasure = r := by
  have hr₀ : 0 < r := by linarith
  have hp : (r : ℂ) * (r⁻¹ : ℝ) = 1 := by exact_mod_cast mul_inv_cancel₀ hr₀.ne'
  rw [quadratic_factor (Complex.ofReal_add r r⁻¹).symm hp, mahlerMeasure_mul,
    mahlerMeasure_X_sub_C, mahlerMeasure_X_sub_C]
  simp [Complex.norm_real, abs_of_pos hr₀,
    max_eq_left (inv_le_one_of_one_le₀ hr.le), max_eq_right hr.le]

-- Five distinct real roots exhaust the degree of the monic trace polynomial.
private lemma tracePoly_factor {a b c d e : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (ha : tracePoly.eval a = 0) (hb : tracePoly.eval b = 0)
    (hc : tracePoly.eval c = 0) (hd : tracePoly.eval d = 0) (he : tracePoly.eval e = 0) :
    tracePoly = (X - C a) * (X - C b) * (X - C c) * (X - C d) * (X - C e) := by
  let roots : Multiset ℝ := a ::ₘ b ::ₘ c ::ₘ d ::ₘ e ::ₘ 0
  have hm : tracePoly.Monic := by unfold tracePoly; monicity!
  have hdeg : tracePoly.natDegree = 5 := by unfold tracePoly; compute_degree!
  have hdistinct : roots.Nodup := by
    simp [roots]
    grind
  have hall : roots = tracePoly.roots := by
    apply Multiset.eq_of_le_of_card_le
    · apply (Multiset.le_iff_subset hdistinct).mpr
      intro x hx
      apply (mem_roots hm.ne_zero).mpr
      change tracePoly.eval x = 0
      simp only [roots, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    · simpa [roots, hdeg] using card_roots' tracePoly
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    (by simp [← hall, roots, hdeg])
  simpa [← hall, roots, mul_assoc] using h.symm

-- Substituting x + x⁻¹ and clearing x⁵ turns each linear factor into a quadratic.
private lemma lehmer_factor {a b c d e : ℝ}
    (h : tracePoly = (X - C a) * (X - C b) * (X - C c) * (X - C d) * (X - C e)) :
    lehmerPolynomial.map (Int.castRingHom ℂ) =
      quadratic a * quadratic b * quadratic c * quadratic d * quadratic e := by
  apply Polynomial.funext
  intro x
  simp [lehmerPolynomial, quadratic]
  by_cases hx : x = 0
  · simp [hx]
  have ht := congrArg (aeval (x + x⁻¹)) h
  simp [tracePoly, map_ofNat] at ht
  linear_combination (norm := (field_simp; ring)) x ^ 5 * ht

private lemma exists_outer_root :
    ∃ r ∈ Set.Ioo (1 : ℝ) (1176281 / 1000000), tracePoly.eval (r + r⁻¹) = 0 := by
  apply intermediate_value_Ioo (by norm_num)
    (f := fun r : ℝ ↦ tracePoly.eval (r + r⁻¹))
  · apply tracePoly.continuous.comp_continuousOn
    exact continuousOn_id.add (continuousOn_id.inv₀ fun x hx ↦ ne_of_gt (lt_of_lt_of_le
      zero_lt_one hx.1))
  · constructor <;> norm_num [tracePoly]

/-- **Mahler measure of Lehmer's polynomial.** The Mahler measure of Lehmer's polynomial is at most
$1176281/1000000 = 1.176281$.

Source: Lehmer (1933), the Mahler measure of Lehmer's polynomial is
`1.176280818...`, hence at most `1.176281`. No root-location computation
for the degree-ten example is formalized here. -/
theorem intMahlerMeasure_lehmerPolynomial_le :
    intMahlerMeasure lehmerPolynomial ≤ 1176281 / 1000000 := by
  obtain ⟨a, ⟨ha₁, ha₂⟩, ha⟩ := intermediate_value_Ioo (show (-2 : ℝ) ≤ -3 / 2 by norm_num)
    tracePoly.continuous.continuousOn (show 0 ∈ _ by constructor <;> norm_num [tracePoly])
  obtain ⟨b, ⟨hb₁, hb₂⟩, hb⟩ := intermediate_value_Ioo' (show (-3 / 2 : ℝ) ≤ -1 by norm_num)
    tracePoly.continuous.continuousOn (show 0 ∈ _ by constructor <;> norm_num [tracePoly])
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    tracePoly.continuous.continuousOn (show 0 ∈ _ by constructor <;> norm_num [tracePoly])
  obtain ⟨d, ⟨hd₁, hd₂⟩, hd⟩ := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num)
    tracePoly.continuous.continuousOn (show 0 ∈ _ by constructor <;> norm_num [tracePoly])
  obtain ⟨r, ⟨hr₁, hr₂⟩, hr⟩ := exists_outer_root
  have hde : d < r + r⁻¹ := by linarith [inv_pos.mpr (show 0 < r by linarith)]
  have h := lehmer_factor (tracePoly_factor (ha₂.trans hb₁) (hb₂.trans hc₁) (hc₂.trans hd₁)
    hde ha hb hc hd hr)
  rw [intMahlerMeasure, mapMahlerMeasure, h]
  simp only [mahlerMeasure_mul, quadratic_mahlerMeasure_of_one_lt hr₁]
  rw [quadratic_mahlerMeasure_of_mem (t := a) (by constructor <;> linarith),
    quadratic_mahlerMeasure_of_mem (t := b) (by constructor <;> linarith),
    quadratic_mahlerMeasure_of_mem (t := c) (by constructor <;> linarith),
    quadratic_mahlerMeasure_of_mem (t := d) (by constructor <;> linarith)]
  simpa using hr₂.le

end MathlibExt.NumberTheory.LehmerConstant
