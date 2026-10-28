/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibExt.Analysis.Complex.HadamardFactorization
import MathlibExt.NumberTheory.SelbergClass.ZeroSum

/-!
# Strong multiplicity one in the Selberg class

A member of the Selberg class is determined by its zeros up to `o(T)`: if the zeros of `F` and
`G` with `Re ρ > 0` and `|Im ρ| ≤ T` agree, with multiplicity, up to a set of size `o(T)`, then
`F = G`. By Landau's formula `∑_{|γ| ≤ T} m_ρ n^ρ = -(T/π) Λ(n) + O(n^{3/2} log² T)`, so the
hypothesis forces `Λ_F(n) = Λ_G(n)` for every `n ≥ 2`, hence `log F = log G`.

## Main statements

* `SelbergClass.eq_of_isLittleO_sum_abs_sub_analyticOrderNatAt`: strong multiplicity one.
-/

open ArithmeticFunction

@[expose] public section

namespace SelbergClass

/-- The completed function has the same order at `z` and at `1 - z̄`. -/
private lemma analyticOrderAt_one_sub_conj_eq (H : ℂ → ℂ) (w : ℂ) (hH : Differentiable ℂ H) (hw : w
    ≠ 0)
    (hrefl : ∀ s, H (1 - starRingEnd ℂ s) = w * starRingEnd ℂ (H s))
    (hfin : ∀ p, analyticOrderAt H p ≠ ⊤) (z : ℂ) :
    analyticOrderAt H (1 - starRingEnd ℂ z) = analyticOrderAt H z := by
  obtain ⟨g, hg, hgz, hev⟩ := ((hH.analyticAt z).analyticOrderAt_ne_top).1 (hfin z)
  rw [← Nat.cast_analyticOrderNatAt (hfin z)]
  set n := analyticOrderNatAt H z
  rw [(hH.analyticAt _).analyticOrderAt_eq_natCast]
  have hK : AnalyticAt ℂ (starRingEnd ℂ ∘ g ∘ starRingEnd ℂ) (starRingEnd ℂ z) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt] at hg ⊢
    have ht : Filter.Tendsto (starRingEnd ℂ) (nhds (starRingEnd ℂ z)) (nhds z) := by
      simpa using (Complex.continuous_conj.tendsto (starRingEnd ℂ z))
    filter_upwards [ht.eventually hg] with v hv
    exact differentiableAt_conj_conj_iff.mpr hv
  have hL : AnalyticAt ℂ (fun u : ℂ => 1 - u) (1 - starRingEnd ℂ z) := by fun_prop
  have hK' : AnalyticAt ℂ (fun u : ℂ => (starRingEnd ℂ ∘ g ∘ starRingEnd ℂ) (1 - u))
      (1 - starRingEnd ℂ z) := by
    have h1 : (1 : ℂ) - (1 - starRingEnd ℂ z) = starRingEnd ℂ z := by ring
    exact AnalyticAt.comp (g := starRingEnd ℂ ∘ g ∘ starRingEnd ℂ) (by rw [h1]; exact hK) hL
  refine ⟨fun u => (-1) ^ n * w * (starRingEnd ℂ ∘ g ∘ starRingEnd ℂ) (1 - u),
    analyticAt_const.mul hK', ?_, ?_⟩
  · simp [hw, hgz]
  · have hφ : Filter.Tendsto (fun u : ℂ => 1 - starRingEnd ℂ u) (nhds (1 - starRingEnd ℂ z))
        (nhds z) := by
      have hc : Continuous (fun u : ℂ => 1 - starRingEnd ℂ u) :=
        continuous_const.sub Complex.continuous_conj
      simpa using hc.tendsto (1 - starRingEnd ℂ z)
    filter_upwards [hφ.eventually hev] with u hu
    have hr := hrefl (1 - starRingEnd ℂ u)
    simp only [map_sub, map_one, Complex.conj_conj, sub_sub_cancel] at hr
    rw [hr, hu]
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, map_one, Complex.conj_conj,
      Function.comp_apply]
    have e : (u - (1 - starRingEnd ℂ z)) ^ n * (-1) ^ n = (1 - u - starRingEnd ℂ z) ^ n := by
      rw [← mul_pow]; ring
    linear_combination (w * starRingEnd ℂ (g (1 - starRingEnd ℂ u))) * e.symm

/-- What the proof needs of a member of `𝒮`: its Euler logarithm and log derivative, finiteness
and location of its zeros, and the reflection of multiplicities across `Re s = 1/2`. -/
private lemma exists_zero_data (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (F : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) :
    ∃ (b : ℕ → ℂ) (X : Finset ℂ), IsEulerLog a b ∧
      (∀ s : ℂ, 1 < s.re → LSeriesHasSum (LSeries.logMul b) s (-deriv F s / F s)) ∧
      (∀ T : ℝ, {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite) ∧
      (∀ ρ, F ρ = 0 → ρ.re ≤ 1) ∧
      (∀ ρ : ℂ, ρ.re = 0 → ρ ∉ X →
        analyticOrderNatAt F ρ = analyticOrderNatAt F (1 - starRingEnd ℂ ρ)) := by
  classical
  obtain ⟨-, ⟨F₀, hF₀, ⟨m, G, β, hGd, hGo, hGF₀⟩, ⟨D₀⟩⟩, ⟨b, θ, hθ, hlog, Cb, hbC⟩, hram⟩ := ha
  have hFF₀ : ∀ s, s ≠ 1 → F s = F₀ s := IsLSeriesContinuation.eqOn_compl_one hF hF₀
  have hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by
    rw [hFF₀ s hs]; exact hGF₀ s hs
  obtain ⟨D⟩ : Nonempty (FunctionalEquation F) := ⟨D₀.congr hFF₀⟩
  obtain ⟨H, hHd, hHrefl, hHr⟩ := exists_completed F G m hGd hGF D
  have hFne1 : ∀ s : ℂ, 1 < s.re → F s ≠ 0 := by
    intro s hs
    rw [hF.1 s hs, (hlog.2 s hs).2]
    exact Complex.exp_ne_zero _
  obtain ⟨hstrip, hH2⟩ := completed_zeros_mem_strip F G H m D hGF hHr hHrefl hFne1
  have hfinH : ∀ p, analyticOrderAt H p ≠ ⊤ := Complex.analyticOrderAt_ne_top_of_differentiable hHd
      hH2
  obtain ⟨X, TX, hTX0, hXre, heqFH, hHG⟩ := exists_finset_completed_zeros_eq F G H m D hF.2 hGd hGF
      hHd hHr hstrip
  obtain ⟨hfinHS, hfinFS, hfinHT⟩ := finite_zeros_of_completed F H X hHd hH2 hstrip heqFH
  have hw0 : D.w ≠ 0 := by
    intro h; have := D.norm_w; rw [h, norm_zero] at this; norm_num at this
  refine ⟨b, X ∪ X.image (fun x => 1 - starRingEnd ℂ x), hlog, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hB : LSeries.abscissaOfAbsConv b ≤ (1 : ℝ) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        (hlog.2 y (by simpa using hy)).1
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hlt : LSeries.abscissaOfAbsConv b < s.re := lt_of_le_of_lt hB (by exact_mod_cast hs)
    have hsum : LSeriesSummable (LSeries.logMul b) s := by
      apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
      rwa [LSeries.abscissaOfAbsConv_logMul]
    have h1 := (LSeries_hasDerivAt hlt).cexp
    have heq : (fun z => Complex.exp (LSeries b z)) =ᶠ[nhds s] F := by
      filter_upwards [hU.mem_nhds hs] with z hz
      rw [hF.1 z hz, (hlog.2 z hz).2]
    have h2 := h1.congr_of_eventuallyEq heq.symm
    have hval : -deriv F s / F s = LSeries (LSeries.logMul b) s := by
      rw [h2.deriv, hF.1 s hs, (hlog.2 s hs).2]
      have := Complex.exp_ne_zero (LSeries b s)
      field_simp
    rw [hval]; exact hsum.LSeriesHasSum
  · intro T
    exact hfinFS T
  · intro ρ h0; by_contra h; push Not at h; exact hFne1 ρ h h0
  · intro ρ hre hX
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hX
    obtain ⟨hX1, hX2⟩ := hX
    have hσ : (1 - starRingEnd ℂ ρ) ∉ X := by
      intro h; exact hX2 _ h (by simp)
    have h1 := (heqFH ρ (by rw [hre]) hX1).2
    have h2 := (heqFH (1 - starRingEnd ℂ ρ) (by simp [hre]) hσ).2
    rw [h1, h2]
    simp only [analyticOrderNatAt, analyticOrderAt_one_sub_conj_eq H D.w hHd hw0 hHrefl hfinH ρ]

/-- The two zero sums of Landau's formula differ by at most `n (2 D(T) + E)`. -/
private lemma norm_sub_zero_sums_le (F G : ℂ → ℂ) (XF XG : Finset ℂ)
    (hfinF : ∀ T : ℝ, {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite)
    (hfinG : ∀ T : ℝ, {ρ : ℂ | G ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite)
    (hreF : ∀ ρ, F ρ = 0 → ρ.re ≤ 1) (hreG : ∀ ρ, G ρ = 0 → ρ.re ≤ 1)
    (hrefF : ∀ ρ : ℂ, ρ.re = 0 → ρ ∉ XF →
      analyticOrderNatAt F ρ = analyticOrderNatAt F (1 - starRingEnd ℂ ρ))
    (hrefG : ∀ ρ : ℂ, ρ.re = 0 → ρ ∉ XG →
      analyticOrderNatAt G ρ = analyticOrderNatAt G (1 - starRingEnd ℂ ρ))
    (n : ℕ) (hn : 1 ≤ n) (T : ℝ) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) -
      (∑ᶠ ρ ∈ {ρ : ℂ | G ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ)‖ ≤
      n * (2 * (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0)},
          |(analyticOrderNatAt F ρ : ℝ) - analyticOrderNatAt G ρ|) +
        ∑ x ∈ XF ∪ XG, |(analyticOrderNatAt F x : ℝ) - analyticOrderNatAt G x|) := by
  classical
  set g : ℂ → ℝ := fun ρ => |(analyticOrderNatAt F ρ : ℝ) - analyticOrderNatAt G ρ| with hg
  set D : ℝ → ℝ := fun T =>
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0)}, g ρ with hD
  set E : ℝ := ∑ x ∈ XF ∪ XG, g x with hE
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => abs_nonneg _
  have hmF : ∀ ρ, F ρ ≠ 0 → analyticOrderNatAt F ρ = 0 := fun ρ h => by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (Or.inr h)]
  have hmG : ∀ ρ, G ρ ≠ 0 → analyticOrderNatAt G ρ = 0 := fun ρ h => by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (Or.inr h)]
  change _ ≤ n * (2 * D T + E)
  have hSF := hfinF T
  have hSG := hfinG T
  set SF := {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T} with hSFdef
  set SG := {ρ : ℂ | G ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T} with hSGdef
  set Sp := {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0)} with hSpdef
  have hSp : Sp.Finite := (hSF.union hSG).subset fun ρ hρ => by
    rcases hρ.2.2 with h | h
    · exact Or.inl ⟨h, hρ.1.le, hρ.2.1⟩
    · exact Or.inr ⟨h, hρ.1.le, hρ.2.1⟩
  set S0 : Finset ℂ := hSF.toFinset ∪ hSG.toFinset with hS0
  have hmem0 : ∀ ρ, ρ ∈ S0 ↔ 0 ≤ ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0) := by
    intro ρ
    simp only [hS0, Finset.mem_union, Set.Finite.mem_toFinset, hSFdef, hSGdef,
      Set.mem_ofPred_eq]
    tauto
  have hZF : ∑ᶠ ρ ∈ SF, (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ =
      ∑ ρ ∈ S0, (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSF]
    apply Finset.sum_subset Finset.subset_union_left
    intro ρ hρ hρF
    rw [Set.Finite.mem_toFinset] at hρF
    obtain ⟨h1, h2, _⟩ := (hmem0 ρ).1 hρ
    have : F ρ ≠ 0 := fun h => hρF ⟨h, h1, h2⟩
    simp [hmF ρ this]
  have hZG : ∑ᶠ ρ ∈ SG, (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ =
      ∑ ρ ∈ S0, (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSG]
    apply Finset.sum_subset Finset.subset_union_right
    intro ρ hρ hρG
    rw [Set.Finite.mem_toFinset] at hρG
    obtain ⟨h1, h2, _⟩ := (hmem0 ρ).1 hρ
    have : G ρ ≠ 0 := fun h => hρG ⟨h, h1, h2⟩
    simp [hmG ρ this]
  have hDT : D T = ∑ ρ ∈ hSp.toFinset, g ρ := finsum_mem_eq_finite_toFinset_sum _ hSp
  -- the sum of `g` over `S0` is at most `2 D(T) + E`
  have hsum : ∑ ρ ∈ S0, g ρ ≤ 2 * D T + E := by
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun ρ => 0 < ρ.re)]
    have hpos : S0.filter (fun ρ => 0 < ρ.re) = hSp.toFinset := by
      ext ρ
      rw [Finset.mem_filter, hmem0, Set.Finite.mem_toFinset]
      simp only [hSpdef, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨_, h2, h3⟩, h4⟩; exact ⟨h4, h2, h3⟩
      · rintro ⟨h4, h2, h3⟩; exact ⟨⟨h4.le, h2, h3⟩, h4⟩
    rw [hpos, ← hDT]
    set A := S0.filter (fun ρ => ¬ 0 < ρ.re) with hA
    rw [← Finset.sum_filter_add_sum_filter_not A (fun ρ => ρ ∈ XF ∪ XG)]
    have hX : ∑ ρ ∈ A.filter (fun ρ => ρ ∈ XF ∪ XG), g ρ ≤ E := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ; exact (Finset.mem_filter.1 hρ).2
      · intro ρ _ _; exact hg0 ρ
    set A' := A.filter (fun ρ => ρ ∉ XF ∪ XG) with hA'
    have hA'mem : ∀ ρ ∈ A', ρ.re = 0 ∧ |ρ.im| ≤ T ∧ ρ ∉ XF ∧ ρ ∉ XG := by
      intro ρ hρ
      rw [hA', Finset.mem_filter, hA, Finset.mem_filter, hmem0] at hρ
      obtain ⟨⟨⟨h1, h2, _⟩, h4⟩, h5⟩ := hρ
      rw [Finset.mem_union, not_or] at h5
      exact ⟨le_antisymm (not_lt.1 h4) h1, h2, h5.1, h5.2⟩
    have hσ : ∀ ρ ∈ A', g ρ = g (1 - starRingEnd ℂ ρ) := by
      intro ρ hρ
      obtain ⟨h1, _, h3, h4⟩ := hA'mem ρ hρ
      simp only [hg, hrefF ρ h1 h3, hrefG ρ h1 h4]
    have hinj : Set.InjOn (fun ρ : ℂ => 1 - starRingEnd ℂ ρ) A' := by
      intro x _ y _ h
      have := congrArg (fun u => starRingEnd ℂ (1 - u)) h
      simpa using this
    have hY : ∑ ρ ∈ A', g ρ ≤ D T := by
      rw [Finset.sum_congr rfl hσ]
      rw [← Finset.sum_image (f := g) (g := fun ρ : ℂ => 1 - starRingEnd ℂ ρ) hinj]
      rw [← Finset.sum_filter_ne_zero, hDT]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ' hρ'
        rw [Finset.mem_filter, Finset.mem_image] at hρ'
        obtain ⟨⟨ρ, hρ, rfl⟩, hne⟩ := hρ'
        obtain ⟨h1, h2, _, _⟩ := hA'mem ρ hρ
        rw [Set.Finite.mem_toFinset]
        refine ⟨by simp [h1], by simpa using h2, ?_⟩
        by_contra hc
        rw [not_or] at hc
        apply hne
        simp only [hg, hmF _ hc.1, hmG _ hc.2, sub_self, abs_zero]
      · intro ρ _ _; exact hg0 ρ
    linarith
  rw [hZF, hZG, ← Finset.sum_sub_distrib]
  calc ‖∑ ρ ∈ S0, ((analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ -
          (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ)‖
      ≤ ∑ ρ ∈ S0, ‖(analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ -
          (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S0, (n : ℝ) * g ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨_, _, h3⟩ := (hmem0 ρ).1 hρ
        have hre : ρ.re ≤ 1 := by
          rcases h3 with h | h
          · exact hreF ρ h
          · exact hreG ρ h
        rw [← sub_mul, norm_mul, mul_comm]
        have e : ‖(analyticOrderNatAt F ρ : ℂ) - (analyticOrderNatAt G ρ : ℂ)‖ = g ρ := by
          rw [hg]
          rw [show (analyticOrderNatAt F ρ : ℂ) - (analyticOrderNatAt G ρ : ℂ) =
            (((analyticOrderNatAt F ρ : ℝ) - (analyticOrderNatAt G ρ : ℝ) : ℝ) : ℂ) by
              push_cast; ring]
          rw [Complex.norm_real, Real.norm_eq_abs]
        rw [e]
        exact mul_le_mul_of_nonneg_right (Complex.norm_natCast_cpow_le_self hn hre) (hg0 ρ)
    _ = n * ∑ ρ ∈ S0, g ρ := by rw [Finset.mul_sum]
    _ ≤ n * (2 * D T + E) := by
        exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)

/-- If `T δ / π ≤ |K| log² T + n (2 D(T) + E)` for `T ≥ 2` with `D(T) = o(T)`, then `δ ≤ 0`. -/
private lemma eq_zero_of_isLittleO (δ K E : ℝ) (n : ℕ) (hn : 2 ≤ n) (D : ℝ → ℝ)
    (hZ : D =o[Filter.atTop] fun T : ℝ => T)
    (hmain : ∀ T : ℝ, 2 ≤ T → T / Real.pi * δ ≤ |K| * Real.log T ^ 2 + n * (2 * D T + E)) :
    δ ≤ 0 := by
  by_contra hne
  have hδ0 : 0 < δ := lt_of_not_ge hne
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set ε := δ / (8 * Real.pi * n) with hε
  set ε' := δ / (4 * Real.pi * (|K| + 1)) with hε'
  have hεp : 0 < ε := by positivity
  have hε'p : 0 < ε' := by positivity
  have hεeq : 4 * Real.pi * (n * 2 * ε) = δ := by
    rw [hε]; field_simp; ring
  have hε'eq : 4 * Real.pi * ((|K| + 1) * ε') = δ := by
    rw [hε']; field_simp
  have hev1 := hZ.def hεp
  have hev2 := (Real.isLittleO_pow_log_id_atTop (n := 2)).def hε'p
  obtain ⟨T, hT1, hT2, hT3⟩ := (hev1.and (hev2.and
    (Filter.eventually_ge_atTop (max 2 (4 * Real.pi * n * |E| / δ + 1))))).exists
  have hT2' : 2 ≤ T := le_trans (le_max_left _ _) hT3
  have hTE : 4 * Real.pi * n * |E| / δ ≤ T := by
    linarith [le_trans (le_max_right _ _) hT3]
  rw [div_le_iff₀ hδ0] at hTE
  have hT0 : 0 < T := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT0] at hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hT0] at hT2
  have hDl : D T ≤ ε * T := le_trans (le_abs_self _) hT1
  have hLl : Real.log T ^ 2 ≤ ε' * T := le_trans (le_abs_self _) hT2
  have hm := hmain T hT2'
  have hm' : 4 * (T * δ) ≤ 4 * Real.pi * (|K| * Real.log T ^ 2 + n * (2 * D T + E)) := by
    have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    have e : 4 * Real.pi * (T / Real.pi * δ) = 4 * (T * δ) := by field_simp
    linarith
  have b1 : 4 * Real.pi * (|K| * Real.log T ^ 2) ≤ T * δ := by
    have h1 : |K| * Real.log T ^ 2 ≤ |K| * (ε' * T) :=
      mul_le_mul_of_nonneg_left hLl (abs_nonneg K)
    have h2 : |K| * (ε' * T) ≤ (|K| + 1) * (ε' * T) := by
      have := mul_pos hε'p hT0; nlinarith
    have h3 : 4 * Real.pi * ((|K| + 1) * (ε' * T)) = T * δ := by
      rw [← hε'eq]; ring
    nlinarith
  have b2 : 4 * Real.pi * (n * (2 * D T)) ≤ T * δ := by
    have h1 : (n : ℝ) * (2 * D T) ≤ n * (2 * (ε * T)) := by gcongr
    have h3 : 4 * Real.pi * (n * (2 * (ε * T))) = T * δ := by
      rw [← hεeq]; ring
    nlinarith
  have b3 : 4 * Real.pi * (n * E) ≤ T * δ := by
    have h1 : (n : ℝ) * E ≤ n * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) hn0.le
    nlinarith
  have hTd : 0 < T * δ := mul_pos hT0 hδ0
  nlinarith

/-- **Strong multiplicity one in the Selberg class.** Let `a, b ∈ 𝒮` with continuations `F`
and `G`. If the zeros `ρ` with `Re ρ > 0` and `|Im ρ| ≤ T`, counted with multiplicity, differ by
`o(T)`, i.e. `∑_ρ |m_F(ρ) - m_G(ρ)| = o(T)` as `T → ∞`, then `a = b`. -/
theorem eq_of_isLittleO_sum_abs_sub_analyticOrderNatAt (a b : ArithmeticFunction ℂ) (ha : a ∈
    selbergClass)
    (hb : b ∈ selbergClass) (F G : ℂ → ℂ) (hF : IsLSeriesContinuation a F) (hG :
        IsLSeriesContinuation b G)
    (hZ : (fun T : ℝ => ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0)},
        |(analyticOrderNatAt F ρ : ℝ) - analyticOrderNatAt G ρ|) =o[Filter.atTop]
      (fun T : ℝ => T)) :
    a = b := by
  classical
  obtain ⟨bF, XF, hlogF, hΛF, hfinF, hreF, hrefF⟩ := exists_zero_data a ha F hF
  obtain ⟨bG, XG, hlogG, hΛG, hfinG, hreG, hrefG⟩ := exists_zero_data b hb G hG
  obtain ⟨CF, hCF⟩ := exists_norm_finsum_zeros_cpow_add_le a ha F hF _ hΛF
  obtain ⟨CG, hCG⟩ := exists_norm_finsum_zeros_cpow_add_le b hb G hG _ hΛG
  set g : ℂ → ℝ := fun ρ => |(analyticOrderNatAt F ρ : ℝ) - analyticOrderNatAt G ρ| with hg
  set D : ℝ → ℝ := fun T =>
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧ (F ρ = 0 ∨ G ρ = 0)}, g ρ with hD
  set E : ℝ := ∑ x ∈ XF ∪ XG, g x with hE
  have hcmp : ∀ n : ℕ, 1 ≤ n → ∀ T : ℝ,
      ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) -
        (∑ᶠ ρ ∈ {ρ : ℂ | G ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ)‖ ≤ n * (2 * D T + E) :=
    fun n hn T => norm_sub_zero_sums_le F G XF XG hfinF hfinG hreF hreG hrefF hrefG n hn T
  have hΛeq : ∀ n : ℕ, 2 ≤ n → LSeries.logMul bF n = LSeries.logMul bG n := by
    intro n hn
    set δ := ‖LSeries.logMul bF n - LSeries.logMul bG n‖ with hδ
    set K : ℝ := (CF + CG) * (n : ℝ) ^ (3 / 2 : ℝ) with hK
    have hπ := Real.pi_pos
    have hmain : ∀ T : ℝ, 2 ≤ T →
        T / Real.pi * δ ≤ |K| * Real.log T ^ 2 + n * (2 * D T + E) := by
      intro T hT
      have h1 := hCF n (by omega) T hT
      have h2 := hCG n (by omega) T hT
      have h3 := hcmp n (by omega) T
      generalize (∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) = ZF at h1 h3
      generalize (∑ᶠ ρ ∈ {ρ : ℂ | G ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt G ρ : ℂ) * (n : ℂ) ^ ρ) = ZG at h2 h3
      have e : ((T : ℂ) / (Real.pi : ℂ)) * (LSeries.logMul bF n - LSeries.logMul bG n) =
          (ZF + T / Real.pi * LSeries.logMul bF n) - (ZG + T / Real.pi * LSeries.logMul bG n) -
            (ZF - ZG) := by ring
      have hT0 : 0 ≤ T := by linarith
      have hnorm : ‖((T : ℂ) / (Real.pi : ℂ)) * (LSeries.logMul bF n - LSeries.logMul bG n)‖ =
          T / Real.pi * δ := by
        rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hT0,
          Real.norm_of_nonneg hπ.le]
      have hl : 0 ≤ Real.log T ^ 2 := sq_nonneg _
      have hKl : (CF * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2) +
          (CG * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2) ≤ |K| * Real.log T ^ 2 := by
        have : (CF * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2) +
            (CG * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2) = K * Real.log T ^ 2 := by
          rw [hK]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (le_abs_self K) hl
      rw [← hnorm, e]
      calc _ ≤ ‖(ZF + T / Real.pi * LSeries.logMul bF n) -
              (ZG + T / Real.pi * LSeries.logMul bG n)‖ + ‖ZF - ZG‖ := norm_sub_le _ _
        _ ≤ (‖ZF + T / Real.pi * LSeries.logMul bF n‖ +
              ‖ZG + T / Real.pi * LSeries.logMul bG n‖) + ‖ZF - ZG‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith
    by_contra hne
    exact (norm_pos_iff.2 (sub_ne_zero.2 hne)).not_ge (eq_zero_of_isLittleO δ K E n hn D hZ hmain)
  have hbeq : bF = bG := by
    funext n
    rcases lt_or_ge n 2 with hn | hn
    · have hnp : ¬ IsPrimePow n := by
        interval_cases n
        · exact not_isPrimePow_zero
        · exact not_isPrimePow_one
      have h1 : bF n = 0 := by by_contra h; exact hnp (hlogF.1 n h)
      have h2 : bG n = 0 := by by_contra h; exact hnp (hlogG.1 n h)
      rw [h1, h2]
    · have := hΛeq n hn
      simp only [LSeries.logMul] at this
      have hl : Complex.log (n : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        have : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        exact_mod_cast this.ne'
      exact mul_left_cancel₀ hl this
  subst hbeq
  have hsa : LSeriesSummable (fun n => a n) 2 :=
    LSeriesSummable_of_forall_norm_le_mul_rpow ha.2.2.2 (by norm_num)
  have hsb : LSeriesSummable (fun n => b n) 2 :=
    LSeriesSummable_of_forall_norm_le_mul_rpow hb.2.2.2 (by norm_num)
  have hA : LSeries.abscissaOfAbsConv (fun n => a n) < ⊤ :=
    lt_of_le_of_lt hsa.abscissaOfAbsConv_le (EReal.coe_lt_top _)
  have hB : LSeries.abscissaOfAbsConv (fun n => b n) < ⊤ :=
    lt_of_le_of_lt hsb.abscissaOfAbsConv_le (EReal.coe_lt_top _)
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine LSeries.eq_of_LSeries_eventually_eq hA hB ?_ hn
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    rw [(hlogF.2 _ hx').2, (hlogG.2 _ hx').2]

end SelbergClass
