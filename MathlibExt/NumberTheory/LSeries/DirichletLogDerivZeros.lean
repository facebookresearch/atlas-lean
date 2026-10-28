/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletLogDeriv
public import MathlibExt.NumberTheory.LSeries.RiemannXiZeros
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import MathlibExt.NumberTheory.LSeries.DirichletLeftHalfPlane
import MathlibExt.NumberTheory.LSeries.ZeroFreeRegion
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# `L'/L(s, χ)` and the zeros of `L(s, χ)` near a height

For a primitive Dirichlet character `χ` modulo `q`, we compare `L'/L(s, χ)` with the sum over the
nontrivial zeros `ρ = β + iγ` of `L(s, χ)`, uniformly in `q`, and deduce that a window of bounded
width around a height `t` contains `O(log (q (|t| + 2)))` zeros. All sums run over a family `z`
listing the zeros of `ξ(s, χ)` with multiplicity; for primitive `χ` these are exactly the
nontrivial zeros of `L(s, χ)`. The character modulo `1`, whose `L`-function is `ζ`, is included.

## Main statements

* `DirichletCharacter.analyticOrderAt_xi_modOne_eq`: for a character mod `1`, `ξ(s, χ)` vanishes
  to the same orders as the Riemann `ξ`.
* `DirichletCharacter.re_mem_Icc_of_analyticOrderAt_xi_ne_zero`: for primitive `χ`, the zeros of
  `ξ(s, χ)` lie in the closed critical strip.
* `DirichletCharacter.exists_logDeriv_LFunction_eq_logDeriv_xi_sub`:
  `L'/L(s, χ) = ξ'/ξ(s, χ) - (log q - log π + ψ((s + a)/2)) / 2`.
* `DirichletCharacter.exists_neg_re_logDeriv_LFunction_add_sum_lt_log`:
  `-Re L'/L(s, χ) + ∑_ρ Re (1 / (s - ρ)) < A log (q (|t| + 2))` for `1 ≤ σ ≤ 2`, `|t| ≥ 2`.
* `DirichletCharacter.exists_tsum_one_div_one_add_sq_sub_im_le_log`:
  `∑_ρ 1 / (1 + (t - γ)²) = O(log (q (|t| + 2)))`.
* `DirichletCharacter.exists_card_le_log_of_abs_sub_im_lt`: the zeros with `|t - γ| < 1` number
  `O(log (q (|t| + 2)))`.
* `DirichletCharacter.exists_norm_logDeriv_LFunction_sub_tsum_le_log`:
  `L'/L(s, χ) = ∑_{|t - γ| < 1} 1 / (s - ρ) + O(log (q (|t| + 2)))` for `-3/2 ≤ σ ≤ 5/2`,
  `|t| ≥ 2`.
-/

@[expose] public section

universe u

open Filter Topology Set ArithmeticFunction LSeries RiemannXi

namespace DirichletCharacter

/-! ### `ξ(s, χ)` against `ξ(s)` and against `L(s, χ)` -/

/-- For a character mod `1`, `ξ(s, χ) = Λ(s)` vanishes to the same orders as the Riemann `ξ`:
away from `0, 1` they differ by the factor `s (s - 1) / 2`, and at `0, 1` neither vanishes to
positive order (`Λ` is not analytic there, and `ξ(0) = ξ(1) = 1/2`). -/
theorem analyticOrderAt_xi_modOne_eq (χ : DirichletCharacter ℂ 1) (w : ℂ) :
    analyticOrderAt (xi χ) w = analyticOrderAt riemannXi w := by
  have hξ : xi χ = completedRiemannZeta := by
    funext s; simp [xi, completedLFunction_modOne_eq]
  rw [hξ]
  have hna1 : ¬ AnalyticAt ℂ completedRiemannZeta 1 := by
    intro h
    have hc : Tendsto (fun s => (s - 1) * completedRiemannZeta s) (𝓝[≠] 1)
        (𝓝 ((1 - 1) * completedRiemannZeta 1)) :=
      (((continuous_sub_right (1 : ℂ)).continuousAt).mul h.continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    have := tendsto_nhds_unique hc completedRiemannZeta_residue_one
    simp at this
  have hna0 : ¬ AnalyticAt ℂ completedRiemannZeta 0 := by
    intro h
    apply hna1
    have hl : AnalyticAt ℂ (fun s : ℂ => 1 - s) 1 := by fun_prop
    have h' : AnalyticAt ℂ (fun s => completedRiemannZeta (1 - s)) 1 :=
      (by simpa using h : AnalyticAt ℂ completedRiemannZeta (1 - 1)).comp hl
    simpa [completedRiemannZeta_one_sub] using h'
  by_cases hw0 : w = 0
  · subst hw0
    rw [analyticOrderAt_of_not_analyticAt hna0]
    symm; rw [analyticOrderAt_eq_zero]; right; simp [riemannXi_zero]
  by_cases hw1 : w = 1
  · subst hw1
    rw [analyticOrderAt_of_not_analyticAt hna1]
    symm; rw [analyticOrderAt_eq_zero]; right; simp [riemannXi_one]
  have hmem : ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) ∈ 𝓝 w :=
    (isOpen_ne.inter isOpen_ne).mem_nhds ⟨hw0, hw1⟩
  have hΛ : AnalyticAt ℂ completedRiemannZeta w :=
    DifferentiableOn.analyticAt
      (fun x hx => (differentiableAt_completedZeta hx.1 hx.2).differentiableWithinAt) hmem
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) w := by fun_prop
  have hev : riemannXi =ᶠ[𝓝 w] (fun s : ℂ => s * (s - 1) / 2) * completedRiemannZeta := by
    filter_upwards [hmem] with s hs
    exact riemannXi_eq_mul_completedRiemannZeta hs.1 hs.2
  have hp0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) w = 0 :=
    analyticOrderAt_eq_zero.mpr
      (Or.inr (div_ne_zero (mul_ne_zero hw0 (sub_ne_zero.mpr hw1)) two_ne_zero))
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hp hΛ, hp0, zero_add]

/-- A primitive character with `χ = 1` has modulus `1`. -/
theorem eq_one_of_isPrimitive_of_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ = 1) : q = 1 := by
  rw [isPrimitive_def, hχ1, conductor_one] at hχ
  exact hχ.symm

/-- For primitive `χ`, including the trivial character mod `1`, the zeros of `ξ(s, χ)` lie in the
closed critical strip. -/
theorem re_mem_Icc_of_analyticOrderAt_xi_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {w : ℂ} (hne : analyticOrderAt (xi χ) w ≠ 0) :
    0 ≤ w.re ∧ w.re ≤ 1 := by
  by_cases hχ1 : χ = 1
  · obtain rfl := eq_one_of_isPrimitive_of_eq_one hχ hχ1
    rw [analyticOrderAt_xi_modOne_eq] at hne
    have h0 : riemannXi w = 0 := by
      by_contra h
      exact hne (analyticOrderAt_eq_zero.mpr (Or.inr h))
    have hm := (riemannXi_eq_zero_iff _).mp h0
    exact ⟨hm.2.1, hm.2.2⟩
  · have h0 : xi χ w = 0 := by
      by_contra h
      exact hne (analyticOrderAt_eq_zero.mpr (Or.inr h))
    have hm := (xi_eq_zero_iff hχ hχ1 _).mp h0
    exact ⟨hm.2.1, hm.2.2.1⟩

/-- For primitive `χ`, a family listing the zeros of `ξ(s, χ)` with multiplicity lies in the
closed critical strip. -/
theorem re_mem_Icc_of_card_eq_analyticOrderAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) (n : ι) :
    0 ≤ (z n).re ∧ (z n).re ≤ 1 := by
  refine re_mem_Icc_of_analyticOrderAt_xi_ne_zero hχ ?_
  rw [← hz]
  exact (ENat.card_ne_zero_iff_nonempty _).mpr ⟨⟨n, rfl⟩⟩

/-- **`L'/L` through `ξ(s, χ)`.** For nonprincipal `χ` mod `N` there is a parity `a ∈ {0, 1}`
such that, wherever `Re s > 0` or `Im s ≠ 0` and `ξ(s, χ) ≠ 0`,
`L'/L(s, χ) = ξ'/ξ(s, χ) - (log N / 2 - log π / 2 + ψ((s + a)/2) / 2)`, with `ψ` the digamma
function. -/
theorem exists_logDeriv_LFunction_eq_logDeriv_xi_sub {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ ∀ s : ℂ, (0 < s.re ∨ s.im ≠ 0) → xi χ s ≠ 0 →
      logDeriv (LFunction χ) s = logDeriv (xi χ) s -
        (Complex.log N / 2 - Complex.log Real.pi / 2 + Complex.digamma ((s + a) / 2) / 2) := by
  obtain ⟨a, ha, hapar, hgf⟩ : ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ (1 - χ (-1)) / 2 = (a : ℂ) ∧
      ∀ w, χ.gammaFactor w = Complex.Gammaℝ (w + a) := by
    rcases χ.even_or_odd with h | h
    · refine ⟨0, Or.inl rfl, ?_, fun w => ?_⟩
      · rw [show χ (-1) = 1 from h]; simp
      · rw [h.gammaFactor_def]; simp
    · refine ⟨1, Or.inr rfl, ?_, fun w => ?_⟩
      · rw [show χ (-1) = -1 from h]; norm_num
      · rw [h.gammaFactor_def]; simp
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
  refine ⟨a, ha, fun s hs hfs => ?_⟩
  set f := xi χ with hf
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun w : ℂ => (N : ℂ) ^ ((w + a) / 2) *
      ((Real.pi : ℂ) ^ (-(w + a) / 2) * Complex.Gamma ((w + a) / 2)) := ⟨_, rfl⟩
  have hxiEq : ∀ w : ℂ, (0 < w.re ∨ w.im ≠ 0) → f w = G w * LFunction χ w := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have hg : χ.gammaFactor w ≠ 0 := by
      rw [hgf, Ne, Complex.Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      rcases hw with hw | hw
      · have := congrArg Complex.re hn
        simp at this
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · have := congrArg Complex.im hn
        exact hw (by simpa using this)
    have hGw : G w = (N : ℂ) ^ ((w + a) / 2) * χ.gammaFactor w := by
      rw [hG, hgf, Complex.Gammaℝ_def]
    rw [hf, xi, hapar, hGw, LFunction_eq_completed_div_gammaFactor χ w (Or.inl hw0),
      mul_assoc, mul_div_cancel₀ _ hg]
  have hopen : IsOpen {w : ℂ | 0 < w.re ∨ w.im ≠ 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).union
      (isOpen_ne_fun Complex.continuous_im continuous_const)
  have hev : f =ᶠ[𝓝 s] fun w => G w * LFunction χ w :=
    eventually_of_mem (hopen.mem_nhds hs) fun w hw => hxiEq w hw
  have hLd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inr hχ1)
  have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGm : ∀ m : ℕ, (s + a) / 2 ≠ -m := by
    intro m hm
    rcases hs with hs | hs
    · have h1 := congrArg Complex.re hm
      simp at h1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · have h1 := congrArg Complex.im hm
      exact hs (by simpa using h1)
  have hlin : HasDerivAt (fun w : ℂ => (w + a) / 2) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).add_const (a : ℂ)).div_const 2
  have hlin' : HasDerivAt (fun w : ℂ => -(w + a) / 2) (-1 / 2) s := by
    simpa using (((hasDerivAt_id s).add_const (a : ℂ)).neg).div_const 2
  have h1 := hlin.const_cpow (c := (N : ℂ)) (Or.inl hNz)
  have h2 := hlin'.const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
  have hΓd : DifferentiableAt ℂ Complex.Gamma ((s + a) / 2) :=
    Complex.differentiableAt_Gamma _ hGm
  have h3 : HasDerivAt (fun w : ℂ => Complex.Gamma ((w + a) / 2))
      (deriv Complex.Gamma ((s + a) / 2) * (1 / 2)) s :=
    hΓd.hasDerivAt.comp s hlin
  have hΓ0 : Complex.Gamma ((s + a) / 2) ≠ 0 := Complex.Gamma_ne_zero hGm
  have hNs : (N : ℂ) ^ ((s + a) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hNz]
  have hπs : (Real.pi : ℂ) ^ (-(s + a) / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
  have hGd := h1.mul (h2.mul h3)
  rw [show ((fun x : ℂ => (N : ℂ) ^ ((x + a) / 2)) * ((fun x : ℂ => (Real.pi : ℂ) ^
    (-(x + a) / 2)) * fun w : ℂ => Complex.Gamma ((w + a) / 2))) = G by
      rw [hG]; rfl] at hGd
  have hGs : G s ≠ 0 := by rw [hG]; exact mul_ne_zero hNs (mul_ne_zero hπs hΓ0)
  have hLs : LFunction χ s ≠ 0 := by
    intro h; apply hfs; rw [hxiEq s hs, h, mul_zero]
  have hLf : logDeriv f s = logDeriv G s + logDeriv (LFunction χ) s := by
    rw [← logDeriv_fun_mul s hGs hLs hGd.differentiableAt hLd, logDeriv_apply, logDeriv_apply,
      hev.deriv_eq, hev.eq_of_nhds]
  have hLG : logDeriv G s = Complex.log N / 2 - Complex.log Real.pi / 2
      + Complex.digamma ((s + a) / 2) / 2 := by
    rw [logDeriv_apply, hGd.deriv, Complex.digamma_def, logDeriv_apply, hG]
    simp only [Pi.mul_apply]
    field_simp
    ring
  rw [hLf, hLG]; ring

/-! ### Families listing the zeros of `ξ(s, χ)` with multiplicity -/

section Family

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- For primitive `χ ≠ 1`, `ξ(s, χ)` is not identically zero near any point: its orders of
vanishing are finite. -/
theorem analyticOrderAt_xi_ne_top (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (w : ℂ) :
    analyticOrderAt (xi χ) w ≠ ⊤ :=
  Complex.analyticOrderAt_ne_top_of_differentiable (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1) w

/-- For primitive `χ ≠ 1`, only finitely many nontrivial zeros of `L(s, χ)` satisfy
`|Im ρ| < T`. -/
theorem finite_setOf_mem_nontrivialZeros_abs_im_lt (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (T : ℝ) : {ρ | ρ ∈ χ.nontrivialZeros ∧ |ρ.im| < T}.Finite := by
  by_contra hinf
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨p, -, hp⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK (by
    rintro ρ ⟨hρ, hρT⟩
    exact Complex.mem_reProdIm.mpr ⟨⟨hρ.2.1, hρ.2.2.1⟩, abs_le.mp hρT.le⟩)
  rw [accPt_iff_frequently_nhdsNE] at hp
  have hd := differentiable_xi hχ1
  have h := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun z _ => hd.analyticAt z) isPreconnected_univ (mem_univ p)
    (hp.mono fun s hs => (xi_eq_zero_iff hχ hχ1 s).mpr hs.1) (mem_univ 0)
  exact xi_zero_ne_zero hχ hχ1 h

variable {ι : Type*} {z : ι → ℂ}

/-- For primitive `χ ≠ 1`, a family listing the zeros of `ξ(s, χ)` with multiplicity consists of
nontrivial zeros of `L(s, χ)`. -/
theorem mem_nontrivialZeros_of_card_eq_analyticOrderAt (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) (n : ι) :
    z n ∈ χ.nontrivialZeros :=
  (xi_eq_zero_iff hχ hχ1 _).mp (Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz n)

/-- For primitive `χ ≠ 1`, a family listing the zeros of `ξ(s, χ)` with multiplicity lists every
nontrivial zero of `L(s, χ)`. -/
theorem exists_eq_of_card_eq_analyticOrderAt (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) {ρ : ℂ}
    (hρ : ρ ∈ χ.nontrivialZeros) : ∃ n, z n = ρ := by
  have h0 : analyticOrderAt (xi χ) ρ ≠ 0 := fun h =>
    (((differentiable_xi hχ1).analyticAt ρ).analyticOrderAt_eq_zero.mp h)
      ((xi_eq_zero_iff hχ hχ1 ρ).mpr hρ)
  rw [← hz] at h0
  obtain ⟨⟨n, hn⟩⟩ := (ENat.card_ne_zero_iff_nonempty _).mp h0
  exact ⟨n, hn⟩

/-- In a family listing the zeros of `ξ(s, χ)` with multiplicity, each zero is listed finitely
often. -/
theorem finite_of_card_eq_analyticOrderAt (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) (p : ℂ) :
    Finite {n // z n = p} :=
  ENat.card_lt_top.mp (by
    rw [hz]; exact lt_top_iff_ne_top.mpr (analyticOrderAt_xi_ne_top hχ hχ1 p))

/-- In a family listing the zeros of `ξ(s, χ)` with multiplicity, only finitely many indices have
`|Im z n| < T`. -/
theorem finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) (T : ℝ) :
    {n | |(z n).im| < T}.Finite := by
  refine ((finite_setOf_mem_nontrivialZeros_abs_im_lt hχ hχ1 T).biUnion fun p _ =>
    (Set.finite_coe_iff.mp (finite_of_card_eq_analyticOrderAt hχ hχ1 hz p) :
      {n | z n = p}.Finite)).subset ?_
  intro n hn
  simp only [mem_iUnion]
  exact ⟨z n, ⟨mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n, hn⟩, rfl⟩

end Family

/-! ### `-Re L'/L` against the zero sum -/

/-- The Hadamard bound for a primitive nonprincipal character on `1 ≤ Re s ≤ 2`, with the zero
terms of any finite subfamily moved to the left. -/
private lemma exists_neg_re_logDeriv_add_sum_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → ∀ F : Finset ι,
          -(logDeriv (LFunction χ) s).re + ∑ n ∈ F, (1 / (s - z n)).re ≤
            Real.log (N * (|s.im| + 2)) / 2 + |C| := by
  classical
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  refine ⟨C, fun N _ χ hχ hχ1 ι z hz s hs1 hs2 F => ?_⟩
  set f := xi χ with hf
  have hd : Differentiable ℂ f := differentiable_xi hχ1
  have hX0 : f 0 ≠ 0 := xi_zero_ne_zero hχ hχ1
  obtain ⟨A, B, hAB⟩ := exists_xi_eq_exp_mul_tprod hχ hχ1 hz
  have hRe := hasSum_re_one_div_of_xi_eq_exp_mul_tprod hχ hχ1 hz hAB
  have hzero : ∀ n, f (z n) = 0 := Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz
  have hz0 : ∀ n, z n ≠ 0 := fun n h => hX0 (h ▸ hzero n)
  have hzre : ∀ n, (z n).re ≤ 1 := fun n =>
    (mem_nontrivialZeros_of_card_eq_analyticOrderAt hχ hχ1 hz n).2.2.1
  have hsum := Complex.summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one hd
    (hasGrowthOrderLE_xi hχ1) hX0 hz
  have hm := Complex.summable_one_div_sub_add_one_div hz0 hsum s
  have hLs : LFunction χ s ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs1
  have hfs : f s ≠ 0 := by
    rw [hf, Ne, xi_eq_zero_iff hχ hχ1]
    exact fun h => hLs h.1
  have hLDs : logDeriv f s = B + ∑' n, (1 / (s - z n) + 1 / z n) :=
    Complex.logDeriv_eq_add_tsum_of_eq_exp_mul_tprod hz0 hsum hAB hzero (hd s) hfs
  obtain ⟨a, ha, hLeq⟩ := exists_logDeriv_LFunction_eq_logDeriv_xi_sub hχ1
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
  have hure : ((s + a) / 2).re = (s.re + a) / 2 := by simp
  have huim : ((s + a) / 2).im = s.im / 2 := by simp
  have hupos : 0 < ((s + a) / 2).re := by rw [hure]; linarith
  have hT1 : HasSum (fun n => (1 / (s - z n)).re)
      ((∑' n, (1 / (s - z n) + 1 / z n)).re + B.re) := by
    have := (Complex.hasSum_re hm.hasSum).sub hRe
    simp only [Complex.add_re, add_sub_cancel_right, sub_neg_eq_add] at this
    exact this
  have hnn : ∀ n, 0 ≤ (1 / (s - z n)).re := fun n => by
    rw [one_div, Complex.inv_re, Complex.sub_re]
    exact div_nonneg (by linarith [hzre n]) (Complex.normSq_nonneg _)
  have hxT : ∑ n ∈ F, (1 / (s - z n)).re ≤ (∑' n, (1 / (s - z n) + 1 / z n)).re + B.re :=
    sum_le_hasSum F (fun j _ => hnn j) hT1
  have hu0 : (s + a) / 2 ≠ 0 := fun h => by rw [h] at hupos; simp at hupos
  have harg : |Complex.arg ((s + a) / 2)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hupos)
  have hCu := hC _ hu0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
  have hun1 : 1 / 2 ≤ ‖(s + a) / 2‖ :=
    le_trans (by rw [hure]; linarith) ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hun2 : ‖(s + a) / 2‖ ≤ |s.im| + 2 := by
    have ha1 : a ≤ 1 := by rcases ha with h | h <;> simp [h]
    calc ‖(s + a) / 2‖ ≤ |((s + a) / 2).re| + |((s + a) / 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re + a) / 2 + |s.im| / 2 := by
          rw [hure, huim, abs_of_pos (by linarith), abs_div, abs_two]
      _ ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hdg : (Complex.digamma ((s + a) / 2)).re ≤ Real.log (|s.im| + 2) + 2 * |C| := by
    have h3 : (Complex.digamma ((s + a) / 2) - Complex.log ((s + a) / 2)).re ≤ 2 * |C| := by
      calc _ ≤ ‖Complex.digamma ((s + a) / 2) - Complex.log ((s + a) / 2)‖ :=
            Complex.re_le_norm _
        _ ≤ C / ‖(s + a) / 2‖ := hCu
        _ ≤ |C| / ‖(s + a) / 2‖ := by gcongr; exact le_abs_self C
        _ ≤ |C| / (1 / 2) := by gcongr
        _ = 2 * |C| := by ring
    rw [Complex.sub_re, Complex.log_re] at h3
    have := Real.log_le_log (by linarith) hun2
    linarith
  rw [hLeq s (Or.inl (by linarith)) hfs, hLDs]
  have hlogN : (Complex.log (N : ℂ)).re = Real.log N := by
    rw [Complex.log_re, Complex.norm_natCast]
  have hlogπ : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, hlogN, hlogπ]
  have hπ1 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNl : Real.log (N * (|s.im| + 2)) = Real.log N + Real.log (|s.im| + 2) :=
    Real.log_mul hN0.ne' (by positivity)
  linarith

/-- **`-Re L'/L` against the zero sum.** There is an absolute constant `A` such that for every
primitive Dirichlet character `χ` mod `q`, every family `z` listing the zeros of `ξ(s, χ)` with
multiplicity (the nontrivial zeros `ρ` of `L(s, χ)`), and every `s = σ + it` with `1 ≤ σ ≤ 2` and
`|t| ≥ 2`, `-Re (L'/L (s, χ)) + ∑_ρ Re (1 / (s - ρ)) < A log (q (|t| + 2))`. The terms of the sum
are nonnegative, so the bound is stated for every finite subfamily. -/
theorem exists_neg_re_logDeriv_LFunction_add_sum_lt_log :
    ∃ A : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ∀ F : Finset ι,
          -(deriv (LFunction χ) s / LFunction χ s).re + ∑ n ∈ F, (1 / (s - z n)).re <
            A * Real.log (q * (|s.im| + 2)) := by
  classical
  obtain ⟨C, hC⟩ := exists_neg_re_logDeriv_add_sum_le.{u}
  obtain ⟨A3, hA3⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum.{u}
  refine ⟨|C| + |A3| + 2, fun {q} _ χ hχ ι z hz s hs1 hs2 ht F => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (|s.im| + 2)) with hℓdef
  have hqt : |s.im| + 2 ≤ q * (|s.im| + 2) := le_mul_of_one_le_left (by positivity) hq1
  have hℓ : 1 < ℓ := by
    rw [hℓdef, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogt : Real.log |s.im| ≤ ℓ := Real.log_le_log (by linarith) (by linarith)
  have hlogt0 : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
  have hA3ℓ : 0 ≤ |A3| * ℓ := mul_nonneg (abs_nonneg _) (by linarith)
  have hCℓ : |C| ≤ |C| * ℓ := le_mul_of_one_le_right (abs_nonneg _) hℓ.le
  have hCℓ0 : 0 ≤ |C| * ℓ := mul_nonneg (abs_nonneg _) (by linarith)
  have hexp : (|C| + |A3| + 2) * ℓ = |C| * ℓ + |A3| * ℓ + 2 * ℓ := by ring
  by_cases hχ1 : χ = 1
  · obtain rfl := eq_one_of_isPrimitive_of_eq_one hχ hχ1
    have hz' : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w := fun w =>
      (hz w).trans (analyticOrderAt_xi_modOne_eq χ w)
    have key := hA3 z hz' s hs1 hs2 ht
    rw [LFunction_modOne_eq]
    have hzmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz'
    have hm := Complex.summable_one_div_sub_add_one_div (ne_zero_of_card_eq_analyticOrderAt hz')
      (summable_norm_rpow_neg_two hz') s
    have hmre : Summable fun n => (1 / (s - z n) + 1 / z n).re := Complex.reCLM.summable hm
    have hnn : ∀ n, 0 ≤ (1 / (s - z n) + 1 / z n).re := fun n =>
      Complex.re_one_div_sub_add_one_div_nonneg (hzmem n).2.1 (hzmem n).2.2 hs1
    have hle : ∀ n ∈ F, (1 / (s - z n)).re ≤ (1 / (s - z n) + 1 / z n).re := by
      intro n _
      rw [Complex.add_re, one_div (z n), Complex.inv_re]
      have : 0 ≤ (z n).re / Complex.normSq (z n) :=
        div_nonneg (hzmem n).2.1 (Complex.normSq_nonneg _)
      linarith
    have hF : ∑ n ∈ F, (1 / (s - z n)).re ≤ ∑' n, (1 / (s - z n) + 1 / z n).re :=
      (Finset.sum_le_sum hle).trans (hmre.sum_le_tsum F (fun n _ => hnn n))
    have h1 : A3 * Real.log |s.im| ≤ |A3| * ℓ :=
      (mul_le_mul_of_nonneg_right (le_abs_self A3) hlogt0).trans
        (mul_le_mul_of_nonneg_left hlogt (abs_nonneg _))
    rw [hexp]
    linarith
  · have h := hC q χ hχ hχ1 z hz s hs1 hs2 F
    rw [logDeriv_apply] at h
    rw [hexp]
    linarith

/-! ### The zeros near a height -/

/-- **The zeros near a height.** There is an absolute constant `C` such that for every primitive
Dirichlet character `χ` mod `q`, every family `z` listing the zeros of `ξ(s, χ)` with multiplicity
(the nontrivial zeros `ρ = β + iγ` of `L(s, χ)`), and every real `t`, the sum
`∑_ρ 1 / (1 + (t - γ)²)` converges and is at most `C log (q (|t| + 2))`. -/
theorem exists_tsum_one_div_one_add_sq_sub_im_le_log :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ t : ℝ, Summable (fun n => 1 / (1 + (t - (z n).im) ^ 2)) ∧
          ∑' n, 1 / (1 + (t - (z n).im) ^ 2) ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_LFunction_add_sum_lt_log.{u}
  set K : ℝ := ∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨132 * (2 * |A| + K / Real.log 2), fun {q} _ χ hχ ι z hz t => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (|t| + 2)) with hℓdef
  have hℓ2 : Real.log 2 ≤ ℓ := by
    apply Real.log_le_log (by norm_num)
    nlinarith [abs_nonneg t]
  -- a comparison ordinate `t'` with `|t'| ≥ 2`
  obtain ⟨t', ht'2, htt', hℓ'⟩ : ∃ t' : ℝ, 2 ≤ |t'| ∧ |t - t'| ≤ 4 ∧
      Real.log (q * (|t'| + 2)) ≤ 2 * ℓ := by
    by_cases ht : 2 ≤ |t|
    · exact ⟨t, ht, by simp, by linarith⟩
    · refine ⟨2, by norm_num, ?_, ?_⟩
      · push Not at ht
        have := abs_lt.mp ht
        rw [abs_le]; constructor <;> linarith
      · rw [hℓdef, ← Real.log_rpow (by positivity)]
        apply Real.log_le_log (by positivity)
        rw [show ((q : ℝ) * (|t| + 2)) ^ (2 : ℝ) = ((q : ℝ) * (|t| + 2)) ^ (2 : ℕ) by
          norm_cast]
        have h4 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        have : (q : ℝ) * 4 ≤ (q : ℝ) ^ 2 * 4 := by nlinarith
        rw [abs_two]
        nlinarith [mul_le_mul h4 h4 (by norm_num) (by linarith)]
  set s : ℂ := (2 : ℂ) + t' * Complex.I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = t' := by simp [hs]
  have key := hA χ hχ z hz s (by rw [hsre]; norm_num) (by rw [hsre]) (by rw [hsim]; exact ht'2)
  simp only [hsim] at key
  have hre_le : (deriv (LFunction χ) s / LFunction χ s).re ≤ K :=
    (Complex.re_le_norm _).trans (norm_logDeriv_LFunction_le_of_two_le_re χ hsre.ge)
  -- termwise comparison
  have hterm : ∀ n, 1 / (1 + (t - (z n).im) ^ 2) ≤ 132 * (1 / (s - z n)).re := by
    intro n
    obtain ⟨hb0, hb1⟩ := re_mem_Icc_of_card_eq_analyticOrderAt hχ hz n
    rw [one_div (s - z n), Complex.inv_re, Complex.sub_re, hsre, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, hsre, hsim]
    set a := 2 - (z n).re with ha
    set d := t' - (z n).im with hd'
    set e := t - (z n).im with he
    have hde : |e - d| ≤ 4 := by rw [he, hd']; simpa using htt'
    have hde2 : (e - d) ^ 2 ≤ 16 := by
      have := sq_abs (e - d); nlinarith [abs_nonneg (e - d)]
    have ha1 : 1 ≤ a := by linarith
    have ha2 : a ≤ 2 := by linarith
    have hpos : 0 < a * a + d * d := by nlinarith
    rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hpos]
    have hd2 : d * d ≤ 2 * e ^ 2 + 32 := by nlinarith [sq_nonneg (e + (e - d))]
    have hae : a * e ^ 2 ≥ e ^ 2 := by nlinarith [sq_nonneg e]
    nlinarith
  have hsumF : ∀ F : Finset ι, ∑ n ∈ F, 1 / (1 + (t - (z n).im) ^ 2) ≤
      132 * (2 * |A| + K / Real.log 2) * ℓ := by
    intro F
    have hF : ∑ n ∈ F, 1 / (1 + (t - (z n).im) ^ 2) ≤ 132 * ∑ n ∈ F, (1 / (s - z n)).re := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun n _ => hterm n
    have hAl : A * Real.log (q * (|t'| + 2)) ≤ |A| * (2 * ℓ) := by
      have h0 : 0 ≤ Real.log (q * (|t'| + 2)) := Real.log_nonneg (by nlinarith [abs_nonneg t'])
      exact (mul_le_mul_of_nonneg_right (le_abs_self A) h0).trans
        (mul_le_mul_of_nonneg_left hℓ' (abs_nonneg _))
    have hKl : K ≤ K / Real.log 2 * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith
    have hexp : 132 * (2 * |A| + K / Real.log 2) * ℓ
        = 132 * (|A| * (2 * ℓ)) + 132 * (K / Real.log 2 * ℓ) := by ring
    have := key F
    rw [hexp]
    linarith
  have hsum : Summable fun n => 1 / (1 + (t - (z n).im) ^ 2) :=
    summable_of_sum_le (fun n => by positivity) hsumF
  exact ⟨hsum, hsum.tsum_le_of_sum_le hsumF⟩

/-- **The local zero count.** There is an absolute constant `C` such that for every primitive
Dirichlet character `χ` mod `q`, every family `z` listing the zeros of `ξ(s, χ)` with multiplicity
(the nontrivial zeros `ρ = β + iγ` of `L(s, χ)`), and every real `t`, at most
`C log (q (|t| + 2))` zeros satisfy `|t - γ| < 1`: every finite set of such indices has at most
that many elements. -/
theorem exists_card_le_log_of_abs_sub_im_lt :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ t : ℝ, ∀ F : Finset ι, (∀ n ∈ F, |t - (z n).im| < 1) →
          (F.card : ℝ) ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{u}
  refine ⟨2 * C, fun {q} _ χ hχ ι z hz t F hF => ?_⟩
  obtain ⟨hs, ht⟩ := hC χ hχ z hz t
  have hsum := (hs.sum_le_tsum F fun n _ => by positivity).trans ht
  have hle : ∀ n ∈ F, (1 / 2 : ℝ) ≤ 1 / (1 + (t - (z n).im) ^ 2) := by
    intro n hn
    have hsq : (t - (z n).im) ^ 2 < 1 := by
      have := abs_lt.mp (hF n hn)
      nlinarith
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hcard : (F.card : ℝ) * (1 / 2) ≤ ∑ n ∈ F, 1 / (1 + (t - (z n).im) ^ 2) := by
    have := Finset.card_nsmul_le_sum F (fun n => 1 / (1 + (t - (z n).im) ^ 2)) (1 / 2) hle
    simpa [nsmul_eq_mul] using this
  linarith

/-! ### `L'/L` near the zeros -/

/-- The logarithmic derivative of the Hadamard product of an entire function of order at most `1`
with `f 0 ≠ 0`, at any point that is not a zero. -/
private lemma exists_logDeriv_eq_add_tsum {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (ho : Complex.HasGrowthOrderLE f 1) (h0 : f 0 ≠ 0) {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) :
    ∃ B : ℂ, (∀ n, z n ≠ 0) ∧ Summable (fun n => ‖z n‖ ^ (-2 : ℝ)) ∧
      ∀ w, (∀ n, z n ≠ w) → f w ≠ 0 ∧ logDeriv f w = B + ∑' n, (1 / (w - z n) + 1 / z n) := by
  obtain ⟨A, B, hAB⟩ := Complex.exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one hd ho h0 hz
  have hzero : ∀ n, f (z n) = 0 := Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz
  have hz0 : ∀ n, z n ≠ 0 := fun n h => h0 (h ▸ hzero n)
  have hsum := Complex.summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one hd ho h0 hz
  refine ⟨B, hz0, hsum, fun w hw => ?_⟩
  have hfw : f w ≠ 0 := by
    intro h
    have hne : analyticOrderAt f w ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨hd.analyticAt w, h⟩
    rw [← hz] at hne
    obtain ⟨⟨n, hn⟩⟩ := (ENat.card_ne_zero_iff_nonempty _).mp hne
    exact hw n hn
  exact ⟨hfw, Complex.logDeriv_eq_add_tsum_of_eq_exp_mul_tprod hz0 hsum hAB hzero (hd w) hfw⟩

/-- The explicit formula for `L'/L` on `-3/2 ≤ σ ≤ 5/2`, `|t| ≥ 2`, for primitive `χ ≠ 1`. -/
private lemma exists_norm_logDeriv_sub_add_tsum_le_of_ne_one :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∃ B : ℂ, (∀ n, z n ≠ 0) ∧ Summable (fun n => ‖z n‖ ^ (-2 : ℝ)) ∧
          ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 → 2 ≤ |w.im| → (∀ n, z n ≠ w) →
            ‖deriv (LFunction χ) w / LFunction χ w - (B + ∑' n, (1 / (w - z n) + 1 / z n))‖ ≤
              Real.log (|w.im| + 2) + C := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_le_log_add
  refine ⟨|Cd| + 1, fun N _ χ hχ hχ1 ι z hz => ?_⟩
  obtain ⟨BH, hz0, hsum, hH⟩ := exists_logDeriv_eq_add_tsum (differentiable_xi hχ1)
    (hasGrowthOrderLE_xi hχ1) (xi_zero_ne_zero hχ hχ1) hz
  obtain ⟨a, ha, hLeq⟩ := exists_logDeriv_LFunction_eq_logDeriv_xi_sub hχ1
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
  have ha1 : a ≤ 1 := by rcases ha with h | h <;> simp [h]
  refine ⟨BH - Complex.log N / 2 + Complex.log Real.pi / 2, hz0, hsum,
    fun s hs1 hs2 ht hzs => ?_⟩
  have himne : s.im ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  obtain ⟨hfs, hLDs⟩ := hH s hzs
  have hGm : ∀ m : ℕ, (s + a) / 2 ≠ -m := by
    intro m hm
    have h1 := congrArg Complex.im hm
    exact himne (by simpa using h1)
  have hrec := Complex.digamma_apply_add_one ((s + a) / 2) hGm
  have hkey : deriv (LFunction χ) s / LFunction χ s
      - (BH - Complex.log N / 2 + Complex.log Real.pi / 2 + ∑' n, (1 / (s - z n) + 1 / z n))
      = -(Complex.digamma ((s + a) / 2 + 1) - ((s + a) / 2)⁻¹) / 2 := by
    rw [← logDeriv_apply, hLeq s (Or.inr himne) hfs, hLDs, hrec]
    ring
  rw [hkey]
  have hu1 : 1 ≤ ‖(s + a) / 2‖ := by
    calc (1 : ℝ) ≤ |((s + a) / 2).im| := by simp [abs_div]; linarith
      _ ≤ _ := Complex.abs_im_le_norm _
  have hv1 : 1 ≤ ‖(s + a) / 2 + 1‖ := by
    calc (1 : ℝ) ≤ |((s + a) / 2 + 1).im| := by simp [abs_div]; linarith
      _ ≤ _ := Complex.abs_im_le_norm _
  have hvre : 0 < ((s + a) / 2 + 1).re := by simp; linarith
  have hv2 : ‖(s + a) / 2 + 1‖ ≤ |s.im| + 2 := by
    calc ‖(s + a) / 2 + 1‖ ≤ |((s + a) / 2 + 1).re| + |((s + a) / 2 + 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = ((s.re + a) / 2 + 1) + |s.im| / 2 := by
          rw [abs_of_pos hvre]; simp [abs_div]
      _ ≤ |s.im| + 2 := by linarith
  have hdg := hCd _ hvre hv1
  have hlog : Real.log ‖(s + a) / 2 + 1‖ ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by linarith) hv2
  have hinv : ‖((s + a) / 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ hu1
  have hl0 : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  rw [norm_div, norm_neg, Complex.norm_two]
  have := norm_sub_le (Complex.digamma ((s + a) / 2 + 1)) ((s + a) / 2)⁻¹
  have := le_abs_self Cd
  have := abs_nonneg Cd
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The explicit formula for `ζ'/ζ` on `-3/2 ≤ σ ≤ 5/2`, `|t| ≥ 2`. -/
private lemma exists_norm_logDeriv_riemannZeta_sub_add_tsum_le :
    ∃ C : ℝ, ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
        ∃ B : ℂ, (∀ n, z n ≠ 0) ∧ Summable (fun n => ‖z n‖ ^ (-2 : ℝ)) ∧
          ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 → 2 ≤ |w.im| → (∀ n, z n ≠ w) →
            ‖deriv riemannZeta w / riemannZeta w - (B + ∑' n, (1 / (w - z n) + 1 / z n))‖ ≤
              Real.log (|w.im| + 2) + C := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_le_log_add
  refine ⟨|Cd| + 1, fun {ι} z hz => ?_⟩
  obtain ⟨BH, hz0, hsum, hH⟩ := exists_logDeriv_eq_add_tsum differentiable_riemannXi
    hasGrowthOrderLE_riemannXi riemannXi_zero_ne_zero hz
  obtain ⟨A₀, B, hAB⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  refine ⟨B + (Real.log Real.pi : ℂ) / 2, hz0, hsum, fun s hs1 hs2 ht hzs => ?_⟩
  have himne : s.im ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hs1' : s ≠ 1 := by rintro rfl; simp at himne
  have hfs := (hH s hzs).1
  have hζ : riemannZeta s ≠ 0 := fun h => hfs (riemannXi_eq_zero_of_riemannZeta_eq_zero himne h)
  have hE := neg_logDeriv_riemannZeta_eq hz hAB hs1' hζ
  rw [logDeriv_apply] at hE
  have hkey : deriv riemannZeta s / riemannZeta s
      - (B + (Real.log Real.pi : ℂ) / 2 + ∑' n, (1 / (s - z n) + 1 / z n))
      = -(1 / (s - 1)) - Complex.digamma (s / 2 + 1) / 2 := by
    linear_combination -hE
  rw [hkey]
  have hvre : 0 < (s / 2 + 1).re := by simp; linarith
  have hv1 : 1 ≤ ‖s / 2 + 1‖ := by
    calc (1 : ℝ) ≤ |(s / 2 + 1).im| := by simp [abs_div]; linarith
      _ ≤ _ := Complex.abs_im_le_norm _
  have hv2 : ‖s / 2 + 1‖ ≤ |s.im| + 2 := by
    calc ‖s / 2 + 1‖ ≤ |(s / 2 + 1).re| + |(s / 2 + 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re / 2 + 1) + |s.im| / 2 := by
          rw [abs_of_pos hvre]; simp [abs_div]
      _ ≤ |s.im| + 2 := by linarith
  have hdg := hCd _ hvre hv1
  have hlog : Real.log ‖s / 2 + 1‖ ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by linarith) hv2
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    calc (1 : ℝ) ≤ |(s - 1).im| := by simp; linarith
      _ ≤ _ := Complex.abs_im_le_norm _
  have hl0 : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have h3 := norm_sub_le (-(1 / (s - 1))) (Complex.digamma (s / 2 + 1) / 2)
  rw [norm_neg, norm_div (Complex.digamma (s / 2 + 1)), Complex.norm_two] at h3
  have := le_abs_self Cd
  have := abs_nonneg Cd
  linarith

/-- **The explicit formula for `L'/L`.** There is an absolute constant `C` such that for every
primitive `χ`, including the character mod `1`, and every family `z` listing the zeros of
`ξ(s, χ)` with multiplicity, there is `B` with
`‖L'/L(w, χ) - (B + ∑_ρ (1 / (w - ρ) + 1 / ρ))‖ ≤ log (|Im w| + 2) + C` for
`-3/2 ≤ Re w ≤ 5/2`, `|Im w| ≥ 2`, `w` not a zero. -/
theorem exists_norm_logDeriv_LFunction_sub_add_tsum_le :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∃ B : ℂ, (∀ n, z n ≠ 0) ∧ Summable (fun n => ‖z n‖ ^ (-2 : ℝ)) ∧
          ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 → 2 ≤ |w.im| → (∀ n, z n ≠ w) →
            ‖deriv (LFunction χ) w / LFunction χ w - (B + ∑' n, (1 / (w - z n) + 1 / z n))‖ ≤
              Real.log (|w.im| + 2) + C := by
  obtain ⟨C1, hC1⟩ := exists_norm_logDeriv_sub_add_tsum_le_of_ne_one.{u}
  obtain ⟨C2, hC2⟩ := exists_norm_logDeriv_riemannZeta_sub_add_tsum_le.{u}
  refine ⟨|C1| + |C2|, fun {q} _ χ hχ ι z hz => ?_⟩
  have h1 := le_abs_self C1
  have h2 := le_abs_self C2
  have h1' := abs_nonneg C1
  have h2' := abs_nonneg C2
  by_cases hχ1 : χ = 1
  · obtain rfl := eq_one_of_isPrimitive_of_eq_one hχ hχ1
    obtain ⟨B, hz0, hsum, hB⟩ := hC2 z fun w => (hz w).trans (analyticOrderAt_xi_modOne_eq χ w)
    refine ⟨B, hz0, hsum, fun w hw1 hw2 hw3 hw4 => ?_⟩
    rw [LFunction_modOne_eq]
    have := hB w hw1 hw2 hw3 hw4
    linarith
  · obtain ⟨B, hz0, hsum, hB⟩ := hC1 q χ hχ hχ1 z hz
    refine ⟨B, hz0, hsum, fun w hw1 hw2 hw3 hw4 => ?_⟩
    have := hB w hw1 hw2 hw3 hw4
    linarith

/-- **`L'/L` near the zeros.** There is an absolute constant `C` such that for every primitive
Dirichlet character `χ` mod `q`, every family `z` listing the zeros of `ξ(s, χ)` with multiplicity
(the nontrivial zeros `ρ = β + iγ` of `L(s, χ)`), and every `s = σ + it` with `-3/2 ≤ σ ≤ 5/2`,
`|t| ≥ 2` and `t` not the ordinate of a zero,
`‖L'/L(s, χ) - ∑_{|t - γ| < 1} 1 / (s - ρ)‖ ≤ C log (q (|t| + 2))`. The sum has finite support. -/
theorem exists_norm_logDeriv_LFunction_sub_tsum_le_log :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ {ι : Type u} (z : ι → ℂ),
        (∀ w, ENat.card {n // z n = w} = analyticOrderAt (xi χ) w) →
        ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → 2 ≤ |s.im| → (∀ n, (z n).im ≠ s.im) →
          ‖deriv (LFunction χ) s / LFunction χ s
              - ∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖
            ≤ C * Real.log (q * (|s.im| + 2)) := by
  classical
  obtain ⟨C0, hC0⟩ := exists_norm_logDeriv_LFunction_sub_add_tsum_le.{u}
  obtain ⟨C2, hC2⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{u}
  set K : ℝ := ∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨2 + 2 * |C0| + K + 8 * |C2|, fun {q} _ χ hχ ι z hz s hs1 hs2 ht hzim => ?_⟩
  obtain ⟨B, hz0, hsum, hE⟩ := hC0 χ hχ z hz
  set t := s.im with htdef
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (|t| + 2)) with hℓdef
  have hqt : |t| + 2 ≤ q * (|t| + 2) := le_mul_of_one_le_left (by positivity) hq1
  have hℓ : 1 < ℓ := by
    rw [hℓdef, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hlt : Real.log (|t| + 2) ≤ ℓ := Real.log_le_log (by positivity) hqt
  have hre := re_mem_Icc_of_card_eq_analyticOrderAt hχ hz
  -- the comparison point `s₀ = 2 + it`
  set s₀ : ℂ := (2 : ℂ) + t * Complex.I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hzs : ∀ n, z n ≠ s := fun n h => hzim n (by rw [h])
  have hzs₀ : ∀ n, z n ≠ s₀ := fun n h => by
    have := (hre n).2; rw [h, hs₀re] at this; norm_num at this
  have hEs := hE s hs1 hs2 ht hzs
  have hEs₀ := hE s₀ (by rw [hs₀re]; norm_num) (by rw [hs₀re]; norm_num)
    (by rw [hs₀im]; exact ht) hzs₀
  rw [hs₀im] at hEs₀
  have hL0 : ‖deriv (LFunction χ) s₀ / LFunction χ s₀‖ ≤ K :=
    norm_logDeriv_LFunction_le_of_two_le_re χ hs₀re.ge
  -- the zero sums
  set w : ι → ℝ := fun n => 1 / (1 + (t - (z n).im) ^ 2) with hw
  obtain ⟨hwsum, hwt⟩ := hC2 χ hχ z hz t
  set g : ι → ℂ := fun n => (1 / (s - z n) + 1 / z n) - (1 / (s₀ - z n) + 1 / z n) with hg
  set nr : ι → ℂ := fun n => if |t - (z n).im| < 1 then 1 / (s - z n) else 0 with hnr
  set h : ι → ℂ := fun n => g n - nr n with hh
  have hms := Complex.summable_one_div_sub_add_one_div hz0 hsum s
  have hms₀ := Complex.summable_one_div_sub_add_one_div hz0 hsum s₀
  have hgs : Summable g := hms.sub hms₀
  have hbound : ∀ n, ‖h n‖ ≤ 8 * w n := by
    intro n
    have hsz : s - z n ≠ 0 := sub_ne_zero.mpr (hzs n).symm
    have hs₀z : s₀ - z n ≠ 0 := sub_ne_zero.mpr (hzs₀ n).symm
    have hn1 : 1 ≤ ‖s₀ - z n‖ := by
      calc (1 : ℝ) ≤ |(s₀ - z n).re| := by
            rw [Complex.sub_re, hs₀re, abs_of_nonneg (by linarith [(hre n).2])]
            linarith [(hre n).2]
        _ ≤ _ := Complex.abs_re_le_norm _
    have hdi : |t - (z n).im| ≤ ‖s₀ - z n‖ := by
      calc |t - (z n).im| = |(s₀ - z n).im| := by rw [Complex.sub_im, hs₀im]
        _ ≤ _ := Complex.abs_im_le_norm _
    have hdi' : |t - (z n).im| ≤ ‖s - z n‖ := by
      calc |t - (z n).im| = |(s - z n).im| := by rw [Complex.sub_im]
        _ ≤ _ := Complex.abs_im_le_norm _
    have hwn : w n = 1 / (1 + (t - (z n).im) ^ 2) := rfl
    by_cases hc : |t - (z n).im| < 1
    · have hhn : h n = -(1 / (s₀ - z n)) := by
        simp only [hh, hg, hnr, ite_eq_left hc]; ring
      rw [hhn, norm_neg, norm_div, norm_one]
      have hsq : (t - (z n).im) ^ 2 < 1 := by
        have := abs_lt.mp hc; nlinarith
      have hw2 : 1 / 2 ≤ w n := by
        rw [hwn]; apply one_div_le_one_div_of_le (by positivity); linarith
      have : 1 / ‖s₀ - z n‖ ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hn1
      linarith
    · push Not at hc
      have hhn : h n = (s₀ - s) / ((s - z n) * (s₀ - z n)) := by
        simp only [hh, hg, hnr, ite_eq_right (not_lt.mpr hc)]
        field_simp
        ring
      rw [hhn, norm_div, norm_mul]
      have hss : ‖s₀ - s‖ ≤ 7 / 2 := by
        calc ‖s₀ - s‖ ≤ |(s₀ - s).re| + |(s₀ - s).im| := Complex.norm_le_abs_re_add_abs_im _
          _ ≤ 7 / 2 := by
            rw [Complex.sub_re, Complex.sub_im, hs₀re, hs₀im, htdef, sub_self, abs_zero,
              add_zero, abs_le]
            constructor <;> linarith
      set d := |t - (z n).im| with hd
      have hd2 : (t - (z n).im) ^ 2 = d ^ 2 := (sq_abs _).symm
      rw [hwn, hd2]
      have hprod : d * d ≤ ‖s - z n‖ * ‖s₀ - z n‖ :=
        mul_le_mul hdi' hdi (by positivity) (norm_nonneg _)
      have hdpos : 0 < d * d := by nlinarith
      rw [div_le_iff₀ (by nlinarith), mul_div_assoc', div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      nlinarith
  have hhs : Summable h := Summable.of_norm_bounded (hwsum.mul_left 8) hbound
  have hnrs : Summable nr := by
    have : nr = fun n => g n - h n := by funext n; simp only [hh]; ring
    rw [this]; exact hgs.sub hhs
  have hht : ‖∑' n, h n‖ ≤ 8 * (C2 * ℓ) := by
    refine (tsum_of_norm_bounded (hwsum.mul_left 8).hasSum hbound).trans ?_
    rw [tsum_mul_left]; linarith
  -- the identity
  have hP : (∑' n, (1 / (s - z n) + 1 / z n)) - (∑' n, (1 / (s₀ - z n) + 1 / z n))
      = ∑' n, g n := (hms.tsum_sub hms₀).symm
  have hgh : ∑' n, g n = ∑' n, nr n + ∑' n, h n := by
    rw [← hnrs.tsum_add hhs]; congr 1; funext n; simp only [hh]; ring
  have hid : deriv (LFunction χ) s / LFunction χ s - ∑' n, nr n =
      (deriv (LFunction χ) s / LFunction χ s - (B + ∑' n, (1 / (s - z n) + 1 / z n)))
      - (deriv (LFunction χ) s₀ / LFunction χ s₀ - (B + ∑' n, (1 / (s₀ - z n) + 1 / z n)))
      + deriv (LFunction χ) s₀ / LFunction χ s₀ + ∑' n, h n := by
    linear_combination hP + hgh
  rw [hid]
  rw [← htdef] at hEs
  have key : ∀ a b c d : ℂ, ‖a - b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := fun a b c d =>
    (norm_add_le _ _).trans (by
      gcongr
      exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  refine (key _ _ _ _).trans ?_
  have hc0 : C0 ≤ |C0| * ℓ :=
    (le_abs_self C0).trans (le_mul_of_one_le_right (abs_nonneg _) hℓ.le)
  have hkl : K ≤ K * ℓ := le_mul_of_one_le_right hK0 hℓ.le
  have hc2 : C2 * ℓ ≤ |C2| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self C2) (by linarith)
  have hexp : (2 + 2 * |C0| + K + 8 * |C2|) * ℓ = 2 * ℓ + 2 * (|C0| * ℓ) + K * ℓ
      + 8 * (|C2| * ℓ) := by ring
  rw [hexp]
  linarith

end DirichletCharacter
