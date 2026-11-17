/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
import Mathlib.Analysis.Calculus.Deriv.Star
import MathlibExt.Analysis.Complex.PhragmenLindelofStrip
import MathlibExt.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Growth of functions in the Selberg class

## Main statements

* `ArithmeticFunction.IsLSeriesContinuation.exists_norm_le_of_re_eq_two`: if
  `a n = O(n ^ (1/2))`, the continuation of `L(a, s)` is bounded on the line `Re s = 2`.
* `SelbergClass.exists_norm_le_mul_rpow_of_differentiable`: an entire member of the Selberg
  class grows at most polynomially in `|Im s|` on the critical strip `0 ≤ Re s ≤ 1`. The proof
  bounds `F` on `Re s = 2` by its Dirichlet series, transfers this to `Re s = -1` through the
  functional equation and Stirling's formula, and interpolates by Phragmén–Lindelöf.
-/

open Complex Filter

@[expose] public section

namespace ArithmeticFunction

/-- If `a n = O(n ^ (1/2))`, the continuation `F` of `L(a, s)` is bounded on the line
`Re s = 2`. -/
theorem IsLSeriesContinuation.exists_norm_le_of_re_eq_two {a : ArithmeticFunction ℂ}
    {F : ℂ → ℂ} (hF : IsLSeriesContinuation a F) {Ca : ℝ}
    (hCa : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ (1 / 2 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re = 2 → ‖F s‖ ≤ B := by
  have hsum2 : LSeriesSummable (fun n => a n) 2 :=
    LSeriesSummable_of_le_const_mul_rpow (x := 3/2) (by norm_num) ⟨Ca, fun n _ => by
      convert hCa n using 3; norm_num⟩
  have hsumn : Summable fun n => ‖LSeries.term (fun n => a n) 2 n‖ := summable_norm_iff.2 hsum2
  refine ⟨∑' n, ‖LSeries.term (fun n => a n) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _),
    fun s hs => ?_⟩
  rw [hF.1 s (by rw [hs]; norm_num), LSeries]
  have heq : (fun n => ‖LSeries.term (fun n => a n) s n‖) =
      fun n => ‖LSeries.term (fun n => a n) 2 n‖ := by
    funext n; simp only [LSeries.norm_term_eq, hs]; norm_num
  calc _ ≤ ∑' n, ‖LSeries.term (fun n => a n) s n‖ := norm_tsum_le_tsum_norm (heq ▸ hsumn)
    _ = _ := by rw [heq]

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

private lemma norm_le_exp_rpow_strip_of_hasGrowthOrderLE (F G : ℂ → ℂ) (m : ℕ) (β : ℝ)
    (hGo : HasGrowthOrderLE G β)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| →
      ‖F s‖ ≤ C * Real.exp (|s.im| ^ (β + (|β| + 1) + 1)) := by
  obtain ⟨C, T₀, hG⟩ := hGo.exists_norm_le_exp_strip (-1) 2 (by norm_num)
  refine ⟨C, max T₀ 1, fun s h1 h2 ht => le_trans ?_ (hG s h1 h2 (le_of_max_le_left ht))⟩
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at ht
  have hn : 1 ≤ ‖s - 1‖ :=
    (le_of_max_le_right ht).trans (by simpa using Complex.abs_im_le_norm (s - 1))
  rw [hGF s hs1, norm_mul, norm_pow]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hn)

private lemma Gamma_mul_add_ne_zero {F0 : ℂ → ℂ} (E : FunctionalEquation F0) :
    ∀ z : ℂ, 0 < z.re → ∀ i, Complex.Gamma (E.α i * z + E.r i) ≠ 0 := by
  intro z hz i
  apply Complex.Gamma_ne_zero_of_re_pos
  have := E.α_pos i
  have := E.r_re_nonneg i
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  positivity

private lemma completed_reflection_of_differentiable (F0 F : ℂ → ℂ) (E : FunctionalEquation F0)
    (hFF0 : ∀ s, s ≠ 1 → F s = F0 s)
    (hent : Differentiable ℂ F) :
    ∀ s, (E.Q : ℂ) ^ s * F s *
        starRingEnd ℂ (∏ i, (Complex.Gamma (E.α i * (1 - starRingEnd ℂ s) + E.r i))⁻¹) =
      E.w * starRingEnd ℂ ((E.Q : ℂ) ^ (1 - starRingEnd ℂ s) * F (1 - starRingEnd ℂ s)) *
        ∏ i, (Complex.Gamma (E.α i * s + E.r i))⁻¹ := by
  have hgam := Gamma_mul_add_ne_zero E
  set P : ℂ → ℂ := fun z => ∏ i, (Complex.Gamma (E.α i * z + E.r i))⁻¹ with hPdef
  have hP : Differentiable ℂ P := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin E.d)),
        Differentiable ℂ (fun z : ℂ => (Complex.Gamma (E.α i * z + E.r i))⁻¹) := fun i _ =>
      Complex.differentiable_one_div_Gamma.comp
        (((differentiable_const _).mul differentiable_id).add (differentiable_const _))
    exact Differentiable.fun_finsetProd this
  set Φ : ℂ → ℂ := fun z => (E.Q : ℂ) ^ z * F z with hΦdef
  have hQ0 : (E.Q : ℂ) ≠ 0 := by exact_mod_cast E.Q_pos.ne'
  have hΦ : Differentiable ℂ Φ := fun z =>
    (differentiableAt_id.const_cpow (Or.inl hQ0)).mul (hent z)
  have hcc : ∀ f : ℂ → ℂ, Differentiable ℂ f →
      Differentiable ℂ (fun s => starRingEnd ℂ (f (1 - starRingEnd ℂ s))) := by
    intro f hf s
    have h1 : DifferentiableAt ℂ (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) (1 - s) :=
      differentiableAt_conj_conj_iff.2 (hf _)
    have h2 := h1.comp s ((differentiable_const 1).sub differentiable_id s)
    have he : (fun s => starRingEnd ℂ (f (1 - starRingEnd ℂ s))) =
        (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) ∘ HSub.hSub 1 := by
      funext z; simp [Function.comp]
    rw [he]; exact h2
  have hnew : ∀ s, Φ s * starRingEnd ℂ (P (1 - starRingEnd ℂ s)) =
      E.w * starRingEnd ℂ (Φ (1 - starRingEnd ℂ s)) * P s := by
    have hL : Differentiable ℂ (fun s => Φ s * starRingEnd ℂ (P (1 - starRingEnd ℂ s))) :=
      hΦ.mul (hcc P hP)
    have hR' : Differentiable ℂ (fun s => E.w * starRingEnd ℂ (Φ (1 - starRingEnd ℂ s)) * P s) :=
      ((differentiable_const _).mul (hcc Φ hΦ)).mul hP
    have hev : (fun s => Φ s * starRingEnd ℂ (P (1 - starRingEnd ℂ s))) =ᶠ[nhds (1/2 : ℂ)]
        (fun s => E.w * starRingEnd ℂ (Φ (1 - starRingEnd ℂ s)) * P s) := by
      have hO : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ nhds (1/2 : ℂ) :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
      filter_upwards [hO] with s hs
      obtain ⟨hs0, hs1⟩ := hs
      have eqn := E.eqn s hs0 hs1
      have hs' : (1 - starRingEnd ℂ s).re = 1 - s.re := by simp
      have hsn : s ≠ 1 := by rintro rfl; norm_num at hs1
      have hsn' : 1 - starRingEnd ℂ s ≠ 1 := by
        intro h; have := congrArg Complex.re h; rw [hs'] at this; norm_num at this; linarith
      rw [← hFF0 s hsn, ← hFF0 _ hsn'] at eqn
      have hg : ∏ i, Complex.Gamma (E.α i * s + E.r i) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i _ => hgam s hs0 i
      have hg' : ∏ i, Complex.Gamma (E.α i * (1 - starRingEnd ℂ s) + E.r i) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i _ => hgam _ (by rw [hs']; linarith) i
      have hcg' : starRingEnd ℂ (∏ i, Complex.Gamma (E.α i * (1 - starRingEnd ℂ s) + E.r i)) ≠ 0 :=
        (map_ne_zero _).2 hg'
      simp only [hΦdef, hPdef, Finset.prod_inv_distrib, map_inv₀, map_mul] at eqn ⊢
      field_simp
      linear_combination eqn
    exact funext_iff.1 (AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hL.analyticAt z)
      (fun z _ => hR'.analyticAt z) hev)
  exact hnew

private lemma exists_norm_le_mul_rpow_line_neg_one (F0 F : ℂ → ℂ) (E : FunctionalEquation F0)
    (hFF0 : ∀ s, s ≠ 1 → F s = F0 s) (hent : Differentiable ℂ F) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s : ℂ, s.re = 2 → ‖F s‖ ≤ B) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ‖F (-1 + t * Complex.I)‖ ≤ C * |t| ^ (1 + ∑ i, 3 * E.α i) := by
  have hstir := fun i =>
    Complex.exists_norm_Gamma_line_two_mul_inv_line_neg_one_le (E.α i) (E.α_pos i) (E.r i)
  choose M T hM0 hMT using hstir
  set T₀ : ℝ := 1 + ∑ i, |T i| with hT₀
  have hT : ∀ i, T i ≤ T₀ := fun i => by
    have := Finset.single_le_sum (f := fun i => |T i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (T i)
    linarith
  have hgam := Gamma_mul_add_ne_zero E
  have hnew := completed_reflection_of_differentiable F0 F E hFF0 hent
  have hQ := E.Q_pos
  set A : ℝ := 1 + ∑ i, 3 * E.α i with hAdef
  have hsumα : 0 ≤ ∑ i, 3 * E.α i := Finset.sum_nonneg fun i _ => by have := E.α_pos i; positivity
  have hA : 0 < A := by linarith
  have hM : 0 ≤ ∏ i, M i := Finset.prod_nonneg fun i _ => hM0 i
  refine ⟨E.Q ^ 3 * B * (∏ i, M i), T₀, by positivity, ?_⟩
  intro t ht
  have ht1 : 1 ≤ |t| := by
    have : 0 ≤ ∑ i, |T i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have ht0 : 0 < |t| := by linarith
  set s : ℂ := -1 + t * Complex.I
  have hs' : 1 - starRingEnd ℂ s = 2 + t * Complex.I := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have h := congrArg norm (hnew s)
  rw [hs'] at h
  simp only [norm_mul, Complex.norm_conj, E.norm_w, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ] at h
  have hsre : s.re = -1 := by simp [s]
  have h2re : (2 + t * Complex.I : ℂ).re = 2 := by simp
  rw [hsre, h2re] at h
  -- the two products
  set p' := ‖∏ i, (Complex.Gamma (E.α i * (2 + t * Complex.I) + E.r i))⁻¹‖ with hp'
  set p := ‖∏ i, (Complex.Gamma (E.α i * s + E.r i))⁻¹‖ with hp
  set Pr := ∏ i, (‖Complex.Gamma (E.α i * (2 + t * Complex.I) + E.r i)‖ *
      ‖(Complex.Gamma (E.α i * (-1 + t * Complex.I) + E.r i))⁻¹‖) with hPr
  have hp'0 : 0 < p' := by
    rw [hp', norm_pos_iff]
    exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (hgam _ (by rw [h2re]; norm_num) i)
  have hpp : p = p' * Pr := by
    rw [hp, hp', hPr, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : ‖Complex.Gamma (E.α i * (2 + t * Complex.I) + E.r i)‖ ≠ 0 :=
      norm_ne_zero_iff.2 (hgam _ (by rw [h2re]; norm_num) i)
    rw [norm_inv (Complex.Gamma (E.α i * (2 + t * Complex.I) + E.r i))]
    field_simp
    rfl
  have hPr : Pr ≤ (∏ i, M i) * |t| ^ A := by
    calc Pr ≤ ∏ i, (M i * |t| ^ (3 * E.α i)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => hMT i t ((hT i).trans ht))
      _ = (∏ i, M i) * |t| ^ (∑ i, 3 * E.α i) := by
          rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht0]
      _ ≤ (∏ i, M i) * |t| ^ A := by
          gcongr
          linarith
  have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun i _ => by positivity
  have hF2 := hB (2 + t * Complex.I) h2re
  rw [hpp] at h
  -- h : Q^(-1) * ‖F s‖ * p' = Q^2 * ‖F (2+tI)‖ * (p' * Pr)
  have hX : ‖F s‖ = E.Q ^ 3 * ‖F (2 + t * Complex.I)‖ * Pr := by
    have hQm : E.Q ^ (-1 : ℝ) = E.Q⁻¹ := Real.rpow_neg_one _
    have hQ2 : E.Q ^ (2 : ℝ) = E.Q ^ 2 := Real.rpow_two _
    rw [hQm, hQ2] at h
    field_simp at h
    linear_combination h
  rw [hX]
  have : 0 < E.Q ^ 3 := by positivity
  calc E.Q ^ 3 * ‖F (2 + t * Complex.I)‖ * Pr ≤ E.Q ^ 3 * B * ((∏ i, M i) * |t| ^ A) := by
        gcongr
    _ = _ := by ring

/-- **Polynomial growth in the critical strip.** If `a` is in the Selberg class and its
continuation `F` is entire, then `F(s) = O(|t|^A)` for some `A > 0` in the strip
`0 ≤ Re s ≤ 1` (for `|t| ≥ 1`, where `t = Im s`). -/
theorem exists_norm_le_mul_rpow_of_differentiable (a : ArithmeticFunction ℂ)
    (ha : a ∈ selbergClass) (F : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) (hent : Differentiable ℂ F) :
    ∃ A > (0 : ℝ), ∃ C, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1 ≤ |s.im| →
      ‖F s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨-, ⟨F0, hF0, ⟨m, G, β, -, hGo, hGF⟩, ⟨E⟩⟩, -, hacoef⟩ := ha
  have hFF0 := hF.eqOn_compl_one hF0
  obtain ⟨Ca, hCa⟩ := hacoef (1/2) (by norm_num)
  obtain ⟨B, hB0, hB⟩ := hF.exists_norm_le_of_re_eq_two hCa
  have hGF' : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by rw [hGF s hs, hFF0 s hs]
  have hgrowth := norm_le_exp_rpow_strip_of_hasGrowthOrderLE F G m β hGo hGF'
  obtain ⟨CQ, T₀, hCQ, hleft⟩ := exists_norm_le_mul_rpow_line_neg_one F0 F E hFF0 hent B hB0 hB
  set A : ℝ := 1 + ∑ i, 3 * E.α i with hAdef
  have hsumα : 0 ≤ ∑ i, 3 * E.α i := Finset.sum_nonneg fun i _ => by have := E.α_pos i; positivity
  have hA : 0 < A := by linarith
  -- bounded part of the left line
  obtain ⟨Bc, hBc⟩ := (isCompact_closedBall (0 : ℂ) (T₀ + 1)).exists_bound_of_continuousOn
    hent.continuous.continuousOn
  set CL : ℝ := max (max CQ Bc) B with hCL
  have hCL0 : 0 ≤ CL := le_trans hB0 (le_max_right _ _)
  have hlines : ∃ C, ∀ s : ℂ, (s.re = -1 ∨ s.re = 2) → 1 ≤ |s.im| → ‖F s‖ ≤ C * |s.im| ^ A := by
    refine ⟨CL, fun s hs ht => ?_⟩
    have hpow : 1 ≤ |s.im| ^ A := Real.one_le_rpow ht hA.le
    have hle : CL ≤ CL * |s.im| ^ A := le_mul_of_one_le_right hCL0 hpow
    rcases hs with hs | hs
    · have hse : s = -1 + (s.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hs]
      rcases le_or_gt T₀ |s.im| with hT0 | hT0
      · have := hleft s.im hT0
        rw [← hse] at this
        calc ‖F s‖ ≤ CQ * |s.im| ^ A := this
          _ ≤ CL * |s.im| ^ A := by
            gcongr
            exact le_trans (le_max_left _ _) (le_max_left _ _)
      · have hmem : s ∈ Metric.closedBall (0 : ℂ) (T₀ + 1) := by
          rw [mem_closedBall_zero_iff]
          have := Complex.norm_le_abs_re_add_abs_im s
          rw [hs] at this
          norm_num at this
          linarith
        calc ‖F s‖ ≤ Bc := hBc s hmem
          _ ≤ CL := le_trans (le_max_right _ _) (le_max_left _ _)
          _ ≤ _ := hle
    · calc ‖F s‖ ≤ B := hB s hs
        _ ≤ CL := le_max_right _ _
        _ ≤ _ := hle
  obtain ⟨C, hC⟩ := PhragmenLindelof.vertical_strip_le_mul_rpow
    (a := -1) (b := 2) hent.diffContOnCl hgrowth hlines
  exact ⟨A, hA, C, fun s h0 h1 ht => hC s (by linarith) (by linarith) ht⟩

end SelbergClass
