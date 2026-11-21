/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import MathlibExt.Analysis.Complex.PhragmenLindelofPolynomial

/-!
# Phragmén–Lindelöf on a vertical strip with polynomial bounds

Mathlib's `PhragmenLindelof.vertical_strip` is stated with an `IsBigO` hypothesis along the
filter of the strip. Here we give versions with explicit pointwise bounds, convenient for
`L`-functions: a function holomorphic on the open strip `a < Re s < b`, continuous on its closure,
of growth at most `exp (|Im s| ^ α)`, is bounded in the strip if it is bounded on the two edges,
and is `O(|Im s| ^ A)` in the strip if it is `O(|Im s| ^ A)` on the two edges.

## Main statements

* `PhragmenLindelof.vertical_strip_of_le_exp_rpow`: boundedness on the edges gives boundedness
  in the strip.
* `PhragmenLindelof.vertical_strip_le_mul_rpow`: polynomial growth `C |Im s| ^ A` on the edges
  gives polynomial growth `C' |Im s| ^ A` in the strip (for `|Im s| ≥ 1`). This repackages
  `PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip` for hypotheses that
  only hold for large `|Im s|`.
-/

open Complex Filter Asymptotics Set

@[expose] public section

namespace PhragmenLindelof

/-- **Phragmén–Lindelöf on a vertical strip.** Let `f` be holomorphic on the open strip
`a < Re s < b` and continuous on its closure, with `‖f s‖ ≤ C exp (|Im s| ^ α)` for large
`|Im s|`. If `f` is bounded on the two edges `Re s = a` and `Re s = b`, then it is bounded on the
closed strip.

Source: E. Phragmén and E. Lindelöf, "Sur une extension d'un principe classique de l'analyse et sur
quelques propriétés des fonctions monogènes dans le voisinage d'un point singulier," Acta Math. 31
(1908), 381–406, DOI 10.1007/BF02415450. Special case: the growth `exp (|Im s| ^ α)` is far inside
the admissible one. -/
theorem vertical_strip_of_le_exp_rpow {f : ℂ → ℂ} {a b α : ℝ}
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hgrowth : ∃ C T₀ : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * Real.exp (|s.im| ^ α))
    (hedge : ∃ B : ℝ, ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖f s‖ ≤ B) :
    ∃ B' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ B' := by
  obtain ⟨C, T₀, hC⟩ := hgrowth
  obtain ⟨B, hB⟩ := hedge
  have hO : ∃ c < Real.pi / (b - a), ∃ B₁, f =O[comap (_root_.abs ∘ im) atTop ⊓
      𝓟 (re ⁻¹' Ioo a b)] fun z ↦ Real.exp (B₁ * Real.exp (c * |z.im|)) := by
    rcases lt_or_ge a b with hab | hab
    · have hc : 0 < Real.pi / (b - a) / 2 := by
        have : 0 < b - a := by linarith
        positivity
      refine ⟨Real.pi / (b - a) / 2, by linarith, 1, ?_⟩
      have hlo := (isLittleO_rpow_exp_pos_mul_atTop α hc).bound one_pos
      have hev : ∀ᶠ x : ℝ in atTop,
          T₀ ≤ x ∧ 0 ≤ x ∧ ‖x ^ α‖ ≤ 1 * ‖Real.exp (Real.pi / (b - a) / 2 * x)‖ :=
        (eventually_ge_atTop T₀).and ((eventually_ge_atTop 0).and hlo)
      refine IsBigO.of_bound C ?_
      have hev' : ∀ᶠ z : ℂ in comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b),
          (T₀ ≤ |z.im| ∧ 0 ≤ |z.im| ∧ ‖|z.im| ^ α‖ ≤
            1 * ‖Real.exp (Real.pi / (b - a) / 2 * |z.im|)‖) ∧ z ∈ re ⁻¹' Ioo a b :=
        inter_mem_inf (preimage_mem_comap hev) (mem_principal_self _)
      filter_upwards [hev'] with z ⟨⟨hT, _, hle⟩, hz⟩
      have h1 := hC z hz.1.le hz.2.le hT
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp] at hle
      rw [Real.norm_eq_abs, Real.abs_exp, one_mul]
      have hC0 : 0 ≤ C := by
        have := (norm_nonneg (f z)).trans h1
        exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
      refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)
      exact (le_abs_self _).trans (by simpa using hle)
    · refine ⟨Real.pi / (b - a) - 1, by linarith, 0, ?_⟩
      have : re ⁻¹' Ioo a b = ∅ := by
        ext z; simp only [mem_preimage, mem_Ioo, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1, h.2]
      rw [this, principal_empty, inf_bot_eq]
      exact IsBigO.of_bound 0 eventually_bot
  exact ⟨B, fun s h1 h2 => vertical_strip hf hO
    (fun z hz => hB z (Or.inl hz)) (fun z hz => hB z (Or.inr hz)) h1 h2⟩

/-- **Polynomial growth on the edges gives polynomial growth in the strip.** Let `f` be
holomorphic on the open strip `a < Re s < b`, continuous on its closure, with
`‖f s‖ ≤ C exp (|Im s| ^ α)` for large `|Im s|`. If `‖f s‖ ≤ C' |Im s| ^ A` on the two edges
for `|Im s| ≥ 1`, with `A ≥ 0`, then `‖f s‖ ≤ C'' |Im s| ^ A` on the closed strip for
`|Im s| ≥ 1`.

Source: E. Phragmén and E. Lindelöf, "Sur une extension d'un principe classique de l'analyse et sur
quelques propriétés des fonctions monogènes dans le voisinage d'un point singulier," Acta Math. 31
(1908), 381–406, DOI 10.1007/BF02415450. Special case: the growth `exp (|Im s| ^ α)` is far inside
the admissible one. -/
theorem vertical_strip_le_mul_rpow {f : ℂ → ℂ} {a b α A : ℝ} (hA : 0 ≤ A)
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hgrowth : ∃ C T₀, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * Real.exp (|s.im| ^ α))
    (hlines : ∃ C, ∀ s : ℂ, (s.re = a ∨ s.re = b) → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A) :
    ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨CL, hCL⟩ := hlines
  rcases le_or_gt b a with hab | hab
  · exact ⟨CL, fun s h1 h2 ht => hCL s (Or.inl (by linarith)) ht⟩
  obtain ⟨C, T₀, hC⟩ := hgrowth
  have hcont : ContinuousOn f (re ⁻¹' Icc a b) := by
    rw [← closure_Ioo hab.ne, ← closure_preimage_re]
    exact hf.continuousOn
  -- `f` is bounded on the bounded parts of the closed strip
  have hrect : ∀ T : ℝ, ∃ K, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ T → ‖f s‖ ≤ K := by
    intro T
    obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_Icc.reProdIm (isCompact_Icc (a := -T) (b := T))) (hcont.mono fun z hz => hz.1)
    exact ⟨K, fun s h1 h2 ht => hK s ⟨⟨h1, h2⟩, abs_le.1 ht⟩⟩
  -- the growth hypothesis gives the double-exponential bound on the whole open strip
  have hc : 0 < Real.pi / (b - a) / 2 := by
    have : 0 < b - a := by linarith
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((isLittleO_rpow_exp_pos_mul_atTop α hc).bound one_pos)
  obtain ⟨K, hK⟩ := hrect (max T₀ N)
  have hgr : ∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
      ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨Real.pi / (b - a) / 2, by linarith, |C| + 1 + |K|, fun z h1 h2 => ?_⟩
    have hE : 1 ≤ Real.exp (Real.pi / (b - a) / 2 * |z.im|) := Real.one_le_exp (by positivity)
    have hE0 := mul_nonneg (abs_nonneg K) (sub_nonneg.2 hE)
    rcases le_or_gt |z.im| (max T₀ N) with ht | ht
    · calc ‖f z‖ ≤ K := hK z h1.le h2.le ht
        _ ≤ Real.exp |K| := (le_abs_self K).trans (by linarith [Real.add_one_le_exp |K|])
        _ ≤ _ := Real.exp_le_exp.2 (by
            nlinarith [mul_nonneg (add_nonneg (abs_nonneg C) zero_le_one) (zero_le_one.trans hE)])
    · have hle := hN _ ((le_max_right _ _).trans ht.le)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp] at hle
      have hpow : |z.im| ^ α ≤ Real.exp (Real.pi / (b - a) / 2 * |z.im|) :=
        (le_abs_self _).trans (by simpa using hle)
      calc ‖f z‖ ≤ C * Real.exp (|z.im| ^ α) := hC z h1.le h2.le ((le_max_left _ _).trans ht.le)
        _ ≤ Real.exp |C| * Real.exp (Real.exp (Real.pi / (b - a) / 2 * |z.im|)) :=
            mul_le_mul ((le_abs_self C).trans (by linarith [Real.add_one_le_exp |C|]))
              (Real.exp_le_exp.2 hpow) (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp (|C| + Real.exp (Real.pi / (b - a) / 2 * |z.im|)) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.2 (by
            nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hE), abs_nonneg K, hE0])
  -- the edge bounds, extended to all heights with the weight `(1 + |Im s|) ^ A`
  obtain ⟨K₁, hK₁⟩ := hrect 1
  have hM : ∀ z : ℂ, (z.re = a ∨ z.re = b) → ‖f z‖ ≤ (|CL| + |K₁|) * (1 + |z.im|) ^ A := by
    intro z hz
    have h1 : a ≤ z.re := by rcases hz with h | h <;> linarith
    have h2 : z.re ≤ b := by rcases hz with h | h <;> linarith
    have hone : 1 ≤ (1 + |z.im|) ^ A := Real.one_le_rpow (by linarith [abs_nonneg z.im]) hA
    rcases le_or_gt 1 |z.im| with ht | ht
    · calc ‖f z‖ ≤ CL * |z.im| ^ A := hCL z hz ht
        _ ≤ |CL| * (1 + |z.im|) ^ A :=
            mul_le_mul (le_abs_self _) (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hA)
              (by positivity) (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg K₁]) (by positivity)
    · calc ‖f z‖ ≤ K₁ := hK₁ z h1 h2 ht.le
        _ ≤ |K₁| * (1 + |z.im|) ^ A := (le_abs_self _).trans (le_mul_of_one_le_right
            (abs_nonneg _) hone)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CL]) (by positivity)
  obtain ⟨C₀, hC₀, hPL⟩ := exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip a b A hab hA
  have hstrip := hPL f (|CL| + |K₁|) (by positivity) hf hgr (fun z hz => hM z (Or.inl hz))
    (fun z hz => hM z (Or.inr hz))
  have hCM : 0 ≤ C₀ * (|CL| + |K₁|) := mul_nonneg hC₀.le (by positivity)
  refine ⟨C₀ * (|CL| + |K₁|) * 2 ^ A, fun s h1 h2 ht => ?_⟩
  calc ‖f s‖ ≤ C₀ * (|CL| + |K₁|) * (1 + |s.im|) ^ A := hstrip s h1 h2
    _ ≤ C₀ * (|CL| + |K₁|) * (2 * |s.im|) ^ A :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hA) hCM
    _ = C₀ * (|CL| + |K₁|) * 2 ^ A * |s.im| ^ A := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]
        ring

end PhragmenLindelof
