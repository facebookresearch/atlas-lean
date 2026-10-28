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
  gives polynomial growth `C' |Im s| ^ A` in the strip (for `|Im s| ≥ 1`).
-/

open Complex Filter Asymptotics Set

@[expose] public section

namespace PhragmenLindelof

/-- **Phragmén–Lindelöf on a vertical strip.** Let `f` be holomorphic on the open strip
`a < Re s < b` and continuous on its closure, with `‖f s‖ ≤ C exp (|Im s| ^ α)` for large
`|Im s|`. If `f` is bounded on the two edges `Re s = a` and `Re s = b`, then it is bounded on the
closed strip. -/
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
for `|Im s| ≥ 1`, then `‖f s‖ ≤ C'' |Im s| ^ A` on the closed strip for `|Im s| ≥ 1`. -/
theorem vertical_strip_le_mul_rpow {f : ℂ → ℂ} {a b α A : ℝ}
    (hf : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hgrowth : ∃ C T₀, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * Real.exp (|s.im| ^ α))
    (hlines : ∃ C, ∀ s : ℂ, (s.re = a ∨ s.re = b) → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A) :
    ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨CL, hCL⟩ := hlines
  rcases le_or_gt b a with hab | hab
  · exact ⟨CL, fun s h1 h2 ht => hCL s (Or.inl (by linarith)) ht⟩
  -- replace `α` by `max α 1 ≥ 1`
  set α' : ℝ := max α 1 with hα'
  have hα : 1 ≤ α' := le_max_right _ _
  replace hgrowth : ∃ C T₀, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * Real.exp (|s.im| ^ α') := by
    obtain ⟨C, T₀, hC⟩ := hgrowth
    refine ⟨C, max T₀ 1, fun s h1 h2 ht => (hC s h1 h2 (le_of_max_le_left ht)).trans ?_⟩
    have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hC s h1 h2 (le_of_max_le_left ht))) (Real.exp_pos _)
    gcongr
    · exact le_of_max_le_right ht
    · exact le_max_left _ _
  set u : ℝ := b + 1 with hu
  set K : ℝ := u - a + 1 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  have hne : ∀ s : ℂ, s.re ≤ b → (u : ℂ) - s ≠ 0 := by
    intro s hs h
    have := congrArg re h
    simp at this; linarith
  have hlow : ∀ s : ℂ, s.re ≤ b → |s.im| ≤ ‖(u : ℂ) - s‖ := by
    intro s hs
    have := abs_im_le_norm ((u : ℂ) - s)
    simpa using this
  have hup : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖(u : ℂ) - s‖ ≤ K * |s.im| := by
    intro s h1 h2 ht
    have := norm_le_abs_re_add_abs_im ((u : ℂ) - s)
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, abs_neg] at this
    rw [abs_of_pos (by linarith)] at this
    nlinarith
  have hpow : ∀ q : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(u : ℂ) - s‖ ^ q ≤ max (K ^ q) 1 * |s.im| ^ q := by
    intro q s h1 h2 ht
    have hx0 : 0 < |s.im| := by linarith
    rcases le_or_gt 0 q with hq | hq
    · calc ‖(u : ℂ) - s‖ ^ q ≤ (K * |s.im|) ^ q :=
            Real.rpow_le_rpow (norm_nonneg _) (hup s h1 h2 ht) hq
        _ = K ^ q * |s.im| ^ q := Real.mul_rpow hKpos.le hx0.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc ‖(u : ℂ) - s‖ ^ q ≤ |s.im| ^ q := Real.rpow_le_rpow_of_nonpos hx0 (hlow s h2) hq.le
        _ = 1 * |s.im| ^ q := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  set g : ℂ → ℂ := fun s => f s * ((u : ℂ) - s) ^ (((-A : ℝ)) : ℂ) with hg
  have hgnorm : ∀ s : ℂ, s.re ≤ b → ‖g s‖ = ‖f s‖ * ‖(u : ℂ) - s‖ ^ (-A) := by
    intro s hs
    simp only [hg, norm_mul]
    rw [norm_cpow_of_ne_zero (hne s hs)]
    simp
  have hclos : closure (re ⁻¹' Ioo a b) ⊆ re ⁻¹' Icc a b :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
  have hgd : DiffContOnCl ℂ g (re ⁻¹' Ioo a b) := by
    have hc : DiffContOnCl ℂ (fun s : ℂ => ((u : ℂ) - s) ^ (((-A : ℝ)) : ℂ))
        (re ⁻¹' Ioo a b) := by
      apply DifferentiableOn.diffContOnCl
      intro s hs
      have hs' := (hclos hs).2
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.cpow_const (differentiableAt_const _ |>.sub differentiableAt_id)
      rw [mem_slitPlane_iff]; left
      simp; linarith
    have := hc.smul hf
    simpa [hg, smul_eq_mul, mul_comm] using this
  have hgg : ∃ C T₀ : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖g s‖ ≤ C * Real.exp (|s.im| ^ (α' + 1)) := by
    obtain ⟨C, T₀, hC⟩ := hgrowth
    have hlo := (isLittleO_rpow_exp_pos_mul_atTop (-A) one_pos).bound one_pos
    obtain ⟨N, hN⟩ := eventually_atTop.1 hlo
    refine ⟨C * max (K ^ (-A)) 1, max (max T₀ 2) N, ?_⟩
    intro s h1 h2 ht
    have hT : T₀ ≤ |s.im| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have h2t : 2 ≤ |s.im| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have hNt : N ≤ |s.im| := le_trans (le_max_right _ _) ht
    set x := |s.im| with hx
    have hf1 := hC s h1 h2 hT
    have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hf1) (Real.exp_pos _)
    have hp := hpow (-A) s h1 h2 (by linarith)
    have hxe : x ^ (-A) ≤ Real.exp x := by
      have := hN x hNt
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, one_mul, one_mul] at this
      exact (le_abs_self _).trans this
    have hxa : x ≤ x ^ α' := by
      calc x = x ^ (1:ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ α' := Real.rpow_le_rpow_of_exponent_le (by linarith) hα
    have hxa1 : x ^ (α' + 1) = x ^ α' * x := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hxa0 : 0 ≤ x ^ α' := by positivity
    have hexp : Real.exp (x ^ α') * Real.exp x ≤ Real.exp (x ^ (α' + 1)) := by
      rw [← Real.exp_add, hxa1]
      apply Real.exp_le_exp.2
      nlinarith
    rw [hgnorm s h2]
    have hM : 0 ≤ max (K ^ (-A)) 1 := le_trans zero_le_one (le_max_right _ _)
    calc ‖f s‖ * ‖(u : ℂ) - s‖ ^ (-A)
        ≤ (C * Real.exp (x ^ α')) * (max (K ^ (-A)) 1 * Real.exp x) := by
          apply mul_le_mul hf1 (hp.trans (mul_le_mul_of_nonneg_left hxe hM)) (by positivity)
          positivity
      _ = C * max (K ^ (-A)) 1 * (Real.exp (x ^ α') * Real.exp x) := by ring
      _ ≤ C * max (K ^ (-A)) 1 * Real.exp (x ^ (α' + 1)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hM)
  have hcont : ContinuousOn g (re ⁻¹' Icc a b) := by
    have : closure (re ⁻¹' Ioo a b) = re ⁻¹' Icc a b := by
      rw [closure_preimage_re, closure_Ioo hab.ne]
    rw [← this]; exact hgd.continuousOn
  obtain ⟨Bc, hBc⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.reProdIm (isCompact_Icc (a := (-1:ℝ)) (b := 1)))
    (hcont.mono (fun z hz => hz.1))
  have hge : ∃ B : ℝ, ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖g s‖ ≤ B := by
    refine ⟨max Bc (CL * max (K ^ (-A)) 1), ?_⟩
    intro s hs
    have h1 : a ≤ s.re := by rcases hs with h | h <;> linarith
    have h2 : s.re ≤ b := by rcases hs with h | h <;> linarith
    rcases le_or_gt 1 |s.im| with ht | ht
    · have hx0 : 0 < |s.im| := by linarith
      have hf1 := hCL s hs ht
      have hp := hpow (-A) s h1 h2 ht
      rw [hgnorm s h2]
      apply le_max_of_le_right
      have hCL0 : 0 ≤ CL * |s.im| ^ A := (norm_nonneg _).trans hf1
      calc ‖f s‖ * ‖(u : ℂ) - s‖ ^ (-A)
          ≤ (CL * |s.im| ^ A) * (max (K ^ (-A)) 1 * |s.im| ^ (-A)) :=
            mul_le_mul hf1 hp (by positivity) hCL0
        _ = CL * max (K ^ (-A)) 1 * (|s.im| ^ A * |s.im| ^ (-A)) := by ring
        _ = CL * max (K ^ (-A)) 1 := by
            rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, mul_one]
    · apply le_max_of_le_left
      apply hBc
      refine ⟨⟨h1, h2⟩, ?_⟩
      have := abs_lt.1 ht
      exact ⟨this.1.le, this.2.le⟩
  obtain ⟨B', hB'⟩ := vertical_strip_of_le_exp_rpow hgd hgg hge
  refine ⟨max B' 0 * max (K ^ A) 1, ?_⟩
  intro s h1 h2 ht
  have hn0 : 0 < ‖(u : ℂ) - s‖ := norm_pos_iff.2 (hne s h2)
  have hfs : ‖f s‖ = ‖g s‖ * ‖(u : ℂ) - s‖ ^ A := by
    rw [hgnorm s h2, mul_assoc, ← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [hfs]
  have hp := hpow A s h1 h2 ht
  calc ‖g s‖ * ‖(u : ℂ) - s‖ ^ A ≤ max B' 0 * (max (K ^ A) 1 * |s.im| ^ A) :=
        mul_le_mul ((hB' s h1 h2).trans (le_max_left _ _)) hp (by positivity) (le_max_right _ _)
    _ = _ := by ring

end PhragmenLindelof
