/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Divisor
import MathlibExt.Analysis.Complex.HadamardFactorization

/-!
# The completed function of a Selberg functional equation

Let `F` satisfy a functional equation `D` of Selberg type (`SelbergClass.FunctionalEquation`)
and let `G` be an entire function with `G(s) = (s - 1)^m F(s)` off `s = 1`. The *completed
function* `H(s) = s^m Q^s ∏ Γ(α_i s + r_i) G(s)` removes the possible pole of `F` at `1` (and,
through the factor `s^m`, the reflected pole at `0`) and continues to an entire function with
`H(1 - s̄) = w · conj (H(s))`. We record its basic properties: its logarithmic derivative, the
relation between its zeros and those of `F`, and the location and finiteness of its zeros.

## Main definitions

* `SelbergClass.FunctionalEquation.congr`: a functional equation transfers to a function agreeing
  off `1`.

## Main statements

* `SelbergClass.exists_completed`: the completed function exists and is entire, with
  `H(1 - s̄) = w · conj (H(s))`.
* `SelbergClass.logDeriv_completed`: the formula for `H'/H` on `Re s > 0`.
* `SelbergClass.completed_eq_zero_iff_and_analyticOrderAt_eq`: away from finitely many points,
  `H` and `F` have the same zeros with the same orders on `Re s ≥ 0`.
* `SelbergClass.completed_zeros_mem_strip`: the zeros of `H` lie in `0 ≤ Re s ≤ 1`.
* `SelbergClass.exists_finset_completed_zeros_eq`: the finite exceptional set.
* `SelbergClass.finite_zeros_of_completed`: zeros up to a given height are finite.
* `Complex.HasGrowthOrderLE.exists_norm_le_exp_strip`: a function of finite order satisfies
  `‖G s‖ ≤ C exp (|Im s| ^ k)` in a vertical strip.
* `logDeriv_one_sub_conj_eq_neg_conj`: `H(1 - s̄) = w H̄(s)` gives
  `H'/H (1 - s̄) = -conj (H'/H (s))`.
* `Complex.finite_setOf_eq_zero_norm_le`: an entire function that is not identically zero has
  finitely many zeros in each closed disc.
-/

open Complex Filter Topology

@[expose] public section

/-- Multiplying by an analytic factor that does not vanish at `s` leaves the order of vanishing
at `s` unchanged. -/
theorem analyticOrderAt_eq_of_eventuallyEq_mul {f g h : ℂ → ℂ} {s : ℂ}
    (hev : f =ᶠ[𝓝 s] fun w => g w * h w)
    (hg : AnalyticAt ℂ g s) (hg0 : g s ≠ 0) (hh : AnalyticAt ℂ h s) :
    analyticOrderAt f s = analyticOrderAt h s := by
  rw [analyticOrderAt_congr hev]
  have : (fun w => g w * h w) = g * h := rfl
  rw [this, analyticOrderAt_mul hg hh, hg.analyticOrderAt_eq_zero.mpr hg0, zero_add]

/-- **Reflection of logarithmic derivatives.** If `H` is entire with
`H(1 - s̄) = w · conj (H(s))` for some `w ≠ 0`, then `H'/H (1 - s̄) = -conj (H'/H (s))`. -/
theorem logDeriv_one_sub_conj_eq_neg_conj (H : ℂ → ℂ) (w : ℂ) (hH : Differentiable ℂ H)
    (hw : w ≠ 0) (hrefl : ∀ s, H (1 - starRingEnd ℂ s) = w * starRingEnd ℂ (H s)) (s : ℂ) :
    logDeriv H (1 - starRingEnd ℂ s) = -starRingEnd ℂ (logDeriv H s) := by
  set K : ℂ → ℂ := starRingEnd ℂ ∘ H ∘ starRingEnd ℂ with hKdef
  have hK : ∀ u, H (1 - u) = w * K u := by
    intro u
    have := hrefl (starRingEnd ℂ u)
    simpa [hKdef] using this
  have hKd : ∀ z, DifferentiableAt ℂ K z := fun z => differentiableAt_conj_conj_iff.mpr (hH _)
  have hKder : ∀ z, deriv K z = starRingEnd ℂ (deriv H (starRingEnd ℂ z)) := by
    intro z
    rw [hKdef, deriv_conj_conj]
    rfl
  have hHeq : H = fun v => w * K (1 - v) := by
    funext v
    rw [← hK (1 - v), sub_sub_cancel]
  set v := 1 - starRingEnd ℂ s with hv
  have hlin : HasDerivAt (fun u : ℂ => 1 - u) (-1) v := by
    simpa using (hasDerivAt_id v).const_sub (1 : ℂ)
  have hd : HasDerivAt H (w * (deriv K (1 - v) * -1)) v := by
    rw [hHeq]
    exact ((hKd (1 - v)).hasDerivAt.comp v hlin).const_mul w
  have h1v : 1 - v = starRingEnd ℂ s := by rw [hv]; ring
  have hHv : H v = w * K (1 - v) := by rw [hHeq]
  rw [logDeriv_apply, logDeriv_apply, hd.deriv, hHv, h1v, hKder]
  simp only [hKdef, Function.comp_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [map_div₀]
  by_cases h0 : H s = 0
  · simp [h0]
  · field_simp

namespace Complex

/-- `Γ` is analytic at every `z ≠ 0` with `Re z ≥ 0`. -/
theorem analyticAt_Gamma_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    AnalyticAt ℂ Gamma z := by
  refine analyticAt_Gamma z fun m hm => hz0 ?_
  have h1 := congrArg re hm
  simp only [neg_re, natCast_re] at h1
  have hm0 : (m : ℝ) = 0 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [hm, show m = 0 by exact_mod_cast hm0]; simp

/-- The digamma function is continuous on the right half-plane `Re w > 0`. -/
theorem continuousAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : ContinuousAt digamma w := by
  refine (analyticAt_digamma w fun m h => ?_).continuousAt
  have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `‖n ^ ρ‖ ≤ n` for `n ≥ 1` and `Re ρ ≤ 1`. -/
theorem norm_natCast_cpow_le_self {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖(n : ℂ) ^ ρ‖ ≤ n := by
  rw [norm_natCast_cpow_of_pos (by omega)]
  calc (n : ℝ) ^ ρ.re ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hρ
    _ = n := Real.rpow_one _

/-- An entire function that is not identically zero has finitely many zeros in each closed
disc `‖ρ‖ ≤ R`. -/
theorem finite_setOf_eq_zero_norm_le {H : ℂ → ℂ} (hH : Differentiable ℂ H) {z0 : ℂ}
    (hz0 : H z0 ≠ 0) (R : ℝ) : {ρ : ℂ | H ρ = 0 ∧ ‖ρ‖ ≤ R}.Finite := by
  set D := MeromorphicOn.divisor H (Metric.closedBall (0 : ℂ) R) with hD
  have hga : AnalyticOnNhd ℂ H (Metric.closedBall (0 : ℂ) R) := fun z _ => hH.analyticAt z
  refine (D.finiteSupport (isCompact_closedBall _ _)).subset fun ρ hρ => ?_
  obtain ⟨h0, hR⟩ := hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff]; exact hR
  rw [Function.mem_support, hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hga hmem]
  have hfin := analyticOrderAt_ne_top_of_differentiable hH hz0 ρ
  have hpos : analyticOrderAt H ρ ≠ 0 := by
    rw [Ne, (hH.analyticAt ρ).analyticOrderAt_eq_zero]
    exact not_not.2 h0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hn] at hpos ⊢
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  exact_mod_cast (by simpa using hpos : n ≠ 0)

/-- **Growth in a vertical strip.** A function of order at most `β` satisfies
`‖G s‖ ≤ C exp (|Im s| ^ (β + (|β| + 1) + 1))` in the strip `σm ≤ Re s ≤ σM` (where
`-σM ≤ σm`) for large `|Im s|`. This is the crude bound needed to apply Phragmén–Lindelöf. -/
theorem HasGrowthOrderLE.exists_norm_le_exp_strip {G : ℂ → ℂ} {β : ℝ}
    (hGo : HasGrowthOrderLE G β) (σm σM : ℝ) (hσ : -σM ≤ σm) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σm ≤ s.re → s.re ≤ σM → T₀ ≤ |s.im| →
      ‖G s‖ ≤ C * Real.exp (|s.im| ^ (β + (|β| + 1) + 1)) := by
  obtain ⟨c, hc, hcG⟩ := (hGo (|β| + 1) (by positivity)).exists_pos
  have hb1 : 1 ≤ β + (|β| + 1) := by have := neg_abs_le β; linarith
  have hev := hcG.bound
  rw [← comap_norm_atTop, eventually_comap, eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  refine ⟨c, max (max R 1) ((σM + 1) ^ (β + (|β| + 1))), fun s h1 h2 ht => ?_⟩
  have ht1 : 1 ≤ |s.im| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htR : R ≤ |s.im| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht3 : (σM + 1) ^ (β + (|β| + 1)) ≤ |s.im| := le_trans (le_max_right _ _) ht
  have hnorm_ge : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have hnorm_le : ‖s‖ ≤ (σM + 1) * |s.im| := by
    have := norm_le_abs_re_add_abs_im s
    have : |s.re| ≤ σM := abs_le.2 ⟨by linarith, h2⟩
    nlinarith
  have hG' := hR ‖s‖ (htR.trans hnorm_ge) s rfl
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hG'
  refine hG'.trans ?_
  gcongr
  calc ‖s‖ ^ (β + (|β| + 1)) ≤ ((σM + 1) * |s.im|) ^ (β + (|β| + 1)) := by gcongr
    _ = (σM + 1) ^ (β + (|β| + 1)) * |s.im| ^ (β + (|β| + 1)) :=
        Real.mul_rpow (by linarith) (abs_nonneg _)
    _ ≤ |s.im| * |s.im| ^ (β + (|β| + 1)) := by gcongr
    _ = |s.im| ^ (β + (|β| + 1) + 1) := by
        rw [Real.rpow_add_one (by positivity)]; ring

end Complex

namespace SelbergClass

open ArithmeticFunction

/-- A functional equation of `F₀` is also a functional equation of any `F` agreeing with `F₀`
off `1` (with the same data, hence the same degree). -/
def FunctionalEquation.congr {F F₀ : ℂ → ℂ} (D₀ : FunctionalEquation F₀)
    (h : ∀ s, s ≠ 1 → F s = F₀ s) : FunctionalEquation F where
  d := D₀.d
  Q := D₀.Q
  α := D₀.α
  r := D₀.r
  w := D₀.w
  Q_pos := D₀.Q_pos
  α_pos := D₀.α_pos
  r_re_nonneg := D₀.r_re_nonneg
  norm_w := D₀.norm_w
  eqn s h0 h1 := by
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    have hs1' : 1 - starRingEnd ℂ s ≠ 1 := by
      intro h; have := congrArg re h; simp at this; linarith
    rw [h s hs1, h _ hs1']
    exact D₀.eqn s h0 h1

/-- Transferring a functional equation does not change its degree. -/
@[simp]
theorem FunctionalEquation.degree_congr {F F₀ : ℂ → ℂ} (D₀ : FunctionalEquation F₀)
    (h : ∀ s, s ≠ 1 → F s = F₀ s) : (D₀.congr h).degree = D₀.degree := rfl

/-- **The completed function.** Let `F` have a functional equation `D` and let `G` be an entire
function with `G(s) = (s - 1)^m F(s)` off `1`. Then the completed function
`H(s) = s^m Q^s ∏ Γ(α_i s + r_i) G(s)`, defined on `Re s > 0`, continues to an entire function
satisfying the reflection `H(1 - s̄) = w · conj (H(s))`. -/
theorem exists_completed (F G : ℂ → ℂ) (m : ℕ) (hGd : Differentiable ℂ G)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (D : FunctionalEquation F) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s)) ∧
      (∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Gamma (D.α i * s + D.r i)) * G s) := by
  have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
  set f1 : ℂ → ℂ := fun s => s ^ m * (D.Q : ℂ) ^ s *
    (∏ i, Gamma (D.α i * s + D.r i)) * G s with hf1
  have hf1d : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ f1 s := by
    intro s hs
    have hP : DifferentiableAt ℂ (fun u => ∏ i, Gamma (D.α i * u + D.r i)) s := by
      apply DifferentiableAt.fun_finsetProd
      intro i _
      apply DifferentiableAt.comp
      · apply differentiableAt_Gamma
        intro k hk
        have := congrArg re hk
        have h3 := re_ofReal_mul_add_pos (D.α_pos i) (D.r_re_nonneg i) hs
        simp only [neg_re, natCast_re] at this
        have h4 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      · exact (differentiableAt_id.const_mul _).add_const _
    exact (((differentiableAt_id.pow m).mul (differentiableAt_id.const_cpow (Or.inl hQ0))).mul
      hP).mul (hGd s)
  have hfe : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      f1 s = D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s)) := by
    intro s h0 h1
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    have hre : (1 - starRingEnd ℂ s).re = 1 - s.re := by simp
    have hs1' : 1 - starRingEnd ℂ s ≠ 1 := by
      intro h; have := congrArg re h; rw [hre] at this; simp at this; linarith
    have eqn := D.eqn s h0 h1
    simp only [hf1]
    rw [hGF s hs1, hGF _ hs1']
    have e1 : (1 - starRingEnd ℂ s - 1) = -starRingEnd ℂ s := by ring
    rw [e1]
    simp only [map_mul, map_pow, map_neg, map_sub, map_one, conj_conj]
    have e2 : s ^ m * (D.Q : ℂ) ^ s * (∏ i, Gamma (D.α i * s + D.r i)) *
        ((s - 1) ^ m * F s) = (s * (s - 1)) ^ m *
          ((D.Q : ℂ) ^ s * (∏ i, Gamma (D.α i * s + D.r i)) * F s) := by
      rw [mul_pow]; ring
    rw [e2, eqn]
    simp only [map_mul]
    have e3 : (s * (s - 1)) ^ m = (1 - s) ^ m * (-s) ^ m := by
      rw [← mul_pow]; congr 1; ring
    rw [e3]
    ring
  set H : ℂ → ℂ := fun s => if 0 < s.re then f1 s else
    D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s)) with hH
  have hHr : ∀ s : ℂ, 0 < s.re → H s = f1 s := fun s hs => ite_eq_left hs
  have hHl : ∀ s : ℂ, s.re < 1 →
      H s = D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s)) := by
    intro s hs
    by_cases h0 : 0 < s.re
    · rw [hHr s h0]; exact hfe s h0 hs
    · exact ite_eq_right h0
  have hgd : ∀ s : ℂ, s.re < 1 →
      DifferentiableAt ℂ (fun s => D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s))) s := by
    intro s hs
    have h1 : DifferentiableAt ℂ (starRingEnd ℂ ∘ f1 ∘ starRingEnd ℂ) (1 - s) := by
      apply differentiableAt_conj_conj_iff.mpr
      apply hf1d
      simp; linarith
    have h2 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s :=
      (differentiableAt_const 1).sub differentiableAt_id
    have h3 := (h1.comp s h2).const_mul D.w
    have e : (fun s => D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s))) =
        fun s => D.w *
          ((starRingEnd ℂ ∘ f1 ∘ starRingEnd ℂ) ∘ fun s : ℂ => 1 - s) s := by
      funext u; simp [Function.comp]
    rw [e]; exact h3
  have hHd : Differentiable ℂ H := by
    intro s
    by_cases h0 : 0 < s.re
    · have hev : H =ᶠ[nhds s] f1 := by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds h0] with u hu
        exact hHr u hu
      exact (hf1d s h0).congr_of_eventuallyEq hev
    · have hs : s.re < 1 := by linarith
      have hev : H =ᶠ[nhds s] (fun s => D.w * starRingEnd ℂ (f1 (1 - starRingEnd ℂ s))) := by
        filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hs] with u hu
        exact hHl u hu
      exact (hgd s hs).congr_of_eventuallyEq hev
  refine ⟨H, hHd, ?_, fun s hs => hHr s hs⟩
  intro s
  have hw : D.w * starRingEnd ℂ D.w = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, D.norm_w]; simp
  by_cases hs : s.re < 1
  · have hre : 0 < (1 - starRingEnd ℂ s).re := by simp; linarith
    rw [hHr _ hre, hHl s hs, map_mul, conj_conj, ← mul_assoc, hw, one_mul]
  · have hre : (1 - starRingEnd ℂ s).re < 1 := by simp; linarith
    have h0 : 0 < s.re := by linarith
    rw [hHl _ hre, hHr s h0]
    congr 2
    simp

/-- **Logarithmic derivative of the completed function.** On `Re s > 0`, away from `s = 1` and
the zeros of `F`, `H'/H = m/s + log Q + ∑ α_i ψ(α_i s + r_i) + m/(s - 1) + F'/F`, where `ψ` is
the digamma function. -/
theorem logDeriv_completed (F G H : ℂ → ℂ) (m : ℕ) (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (D : FunctionalEquation F)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Gamma (D.α i * s + D.r i)) * G s)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hF0 : F s ≠ 0) :
    logDeriv H s = (m : ℂ) / s + log D.Q +
      (∑ i, (D.α i : ℂ) * digamma (D.α i * s + D.r i)) + (m : ℂ) / (s - 1) +
        logDeriv F s := by
  have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hre : ∀ i, 0 < (D.α i * s + D.r i).re := by
    intro i
    simp only [add_re, re_ofReal_mul]
    have := D.α_pos i; have := D.r_re_nonneg i; have := mul_pos (D.α_pos i) hs; linarith
  have hnp : ∀ i, ∀ k : ℕ, (D.α i : ℂ) * s + D.r i ≠ -k := by
    intro i k h
    have := congrArg re h
    have := hre i
    simp only [neg_re, natCast_re] at *
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set f1 : ℂ → ℂ := fun u => (u ^ m * (D.Q : ℂ) ^ u * ∏ i, Gamma (D.α i * u + D.r i)) *
    ((u - 1) ^ m * F u) with hf1
  have hev : H =ᶠ[nhds s] f1 := by
    have hO : {u : ℂ | 0 < u.re ∧ u ≠ 1} ∈ nhds s :=
      ((isOpen_lt continuous_const continuous_re).inter isOpen_ne).mem_nhds ⟨hs, hs1⟩
    filter_upwards [hO] with u hu
    rw [hHr u hu.1, hGF u hu.2]
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  have hFda : DifferentiableAt ℂ F s := hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)
  have hGam : ∀ i, DifferentiableAt ℂ (fun u : ℂ => Gamma (D.α i * u + D.r i)) s := by
    intro i
    exact (differentiableAt_Gamma _ (hnp i)).comp s
      ((differentiableAt_id.const_mul _).add_const _)
  have hGam0 : ∀ i, Gamma (D.α i * s + D.r i) ≠ 0 := fun i => Gamma_ne_zero (hnp i)
  have hP : DifferentiableAt ℂ (fun u => ∏ i, Gamma (D.α i * u + D.r i)) s :=
    DifferentiableAt.fun_finsetProd fun i _ => hGam i
  have hP0 : ∏ i, Gamma (D.α i * s + D.r i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => hGam0 i
  have hcp : DifferentiableAt ℂ (fun u : ℂ => (D.Q : ℂ) ^ u) s :=
    differentiableAt_id.const_cpow (Or.inl hQ0)
  have hcp0 : (D.Q : ℂ) ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero hs0).mpr hQ0
  have hpw : DifferentiableAt ℂ (fun u : ℂ => u ^ m) s := differentiableAt_id.pow m
  have hpw1 : DifferentiableAt ℂ (fun u : ℂ => (u - 1) ^ m) s :=
    (differentiableAt_id.sub_const 1).pow m
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [hf1, logDeriv_fun_mul (f := fun u => u ^ m * (D.Q : ℂ) ^ u *
      ∏ i, Gamma (D.α i * u + D.r i)) (g := fun u => (u - 1) ^ m * F u) s
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs0) hcp0) hP0)
      (mul_ne_zero (pow_ne_zero _ hsub0) hF0) ((hpw.mul hcp).mul hP) (hpw1.mul hFda),
    logDeriv_fun_mul (f := fun u => u ^ m * (D.Q : ℂ) ^ u)
      (g := fun u => ∏ i, Gamma (D.α i * u + D.r i)) s
      (mul_ne_zero (pow_ne_zero _ hs0) hcp0) hP0 (hpw.mul hcp) hP,
    logDeriv_fun_mul (f := fun u : ℂ => u ^ m) (g := fun u : ℂ => (D.Q : ℂ) ^ u) s
      (pow_ne_zero _ hs0) hcp0 hpw hcp,
    logDeriv_fun_mul (f := fun u : ℂ => (u - 1) ^ m) (g := F) s (pow_ne_zero _ hsub0) hF0 hpw1
      hFda,
    logDeriv_fun_prod (fun i _ => hGam0 i) (fun i _ => hGam i)]
  have h1 : logDeriv (fun u : ℂ => u ^ m) s = (m : ℂ) / s := logDeriv_pow s m
  have h2 : logDeriv (fun u : ℂ => (D.Q : ℂ) ^ u) s = log D.Q := by
    rw [logDeriv_apply, ((hasStrictDerivAt_const_cpow (Or.inl hQ0)).hasDerivAt).deriv]
    field_simp
  have h3 : ∀ i, logDeriv (fun u : ℂ => Gamma (D.α i * u + D.r i)) s =
      (D.α i : ℂ) * digamma (D.α i * s + D.r i) := by
    intro i
    have hlin : HasDerivAt (fun u : ℂ => (D.α i : ℂ) * u + D.r i) (D.α i : ℂ) s := by
      simpa using ((hasDerivAt_id s).const_mul (D.α i : ℂ)).add_const (D.r i)
    have := logDeriv_comp (f := Gamma) (g := fun u : ℂ => (D.α i : ℂ) * u + D.r i)
      (differentiableAt_Gamma _ (hnp i)) hlin.differentiableAt
    rw [Function.comp_def] at this
    rw [this, hlin.deriv, mul_comm]
    rfl
  have h4 : logDeriv (fun u : ℂ => (u - 1) ^ m) s = (m : ℂ) / (s - 1) := by
    rw [logDeriv_fun_pow (differentiableAt_id.sub_const 1) m, logDeriv_apply]
    have : deriv (fun u : ℂ => u - 1) s = 1 := by
      simp
    rw [this]; ring
  rw [h1, h2, h4, Finset.sum_congr rfl fun i _ => h3 i]
  ring

/-- **Zeros of the completed function.** On `Re s ≥ 0`, away from `0`, `1` and the points
`-r_i/α_i`, the completed function `H` and `F` have the same zeros, with the same orders. -/
theorem completed_eq_zero_iff_and_analyticOrderAt_eq (F G H : ℂ → ℂ) (m : ℕ)
    (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (hGd : Differentiable ℂ G) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (D : FunctionalEquation F)
    (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Gamma (D.α i * s + D.r i)) * G s)
    (ρ : ℂ) (h0 : 0 ≤ ρ.re) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hpole : ∀ i, D.α i * ρ + D.r i ≠ 0) :
    (H ρ = 0 ↔ F ρ = 0) ∧ analyticOrderAt H ρ = analyticOrderAt F ρ := by
  have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
  set u : ℂ → ℂ := fun s => s ^ m * (D.Q : ℂ) ^ s * ∏ i, Gamma (D.α i * s + D.r i)
    with hu
  have hre : ∀ i, 0 ≤ (D.α i * ρ + D.r i).re := by
    intro i
    simp only [add_re, re_ofReal_mul]
    have := D.α_pos i; have := D.r_re_nonneg i; positivity
  have hua : AnalyticAt ℂ u ρ := by
    have hP : AnalyticAt ℂ (fun s => ∏ i, Gamma (D.α i * s + D.r i)) ρ := by
      apply Finset.analyticAt_fun_prod
      intro i _
      have hl : AnalyticAt ℂ (fun s : ℂ => (D.α i : ℂ) * s + D.r i) ρ := by fun_prop
      exact AnalyticAt.comp (f := fun s : ℂ => (D.α i : ℂ) * s + D.r i)
        (Complex.analyticAt_Gamma_of_re_nonneg (hre i) (hpole i)) hl
    have hc : AnalyticAt ℂ (fun s : ℂ => (D.Q : ℂ) ^ s) ρ := by
      have : (fun s : ℂ => (D.Q : ℂ) ^ s) = fun s => exp (log D.Q * s) := by
        funext s; rw [cpow_def_of_ne_zero hQ0]
      rw [this]
      exact analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
    exact ((analyticAt_id.pow m).mul hc).mul hP
  have hu0 : u ρ ≠ 0 := by
    simp only [hu]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hρ0) ?_) ?_
    · exact (cpow_ne_zero_iff_of_exponent_ne_zero hρ0).mpr hQ0
    · refine Finset.prod_ne_zero_iff.2 fun i _ => Gamma_ne_zero ?_
      intro k hk
      have h1 := congrArg re hk
      have h2 := hre i
      simp only [neg_re, natCast_re] at h1
      have hk0 : (k : ℝ) = 0 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      apply hpole i
      rw [hk]; simp [show k = 0 by exact_mod_cast hk0]
  have hρU : ({1}ᶜ : Set ℂ) ∈ nhds ρ := isOpen_compl_singleton.mem_nhds hρ1
  have hFa : AnalyticAt ℂ F ρ := hFd.analyticAt hρU
  have hGF' : G =ᶠ[nhds ρ] fun s => (s - 1) ^ m * F s := by
    filter_upwards [hρU] with s hs
    exact hGF s hs
  have hGo : analyticOrderAt G ρ = analyticOrderAt F ρ :=
    analyticOrderAt_eq_of_eventuallyEq_mul hGF' ((analyticAt_id.sub analyticAt_const).pow m)
      (pow_ne_zero _ (sub_ne_zero.2 hρ1)) hFa
  have hHf : H =ᶠ[nhds ρ] fun s => u s * G s := by
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · have hfa : AnalyticAt ℂ (fun s => u s * G s) ρ := hua.mul (hGd.analyticAt ρ)
      refine ((hHd.analyticAt ρ).frequently_eq_iff_eventually_eq hfa).1 ?_
      have hne : (nhdsWithin ρ {z : ℂ | 0 < z.re}).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_setOfPred_lt_re]
        exact h0
      have hle : nhdsWithin ρ {z : ℂ | 0 < z.re} ≤ nhdsWithin ρ {ρ}ᶜ := by
        apply nhdsWithin_mono
        intro z hz hzρ
        rw [Set.mem_singleton_iff] at hzρ
        rw [hzρ] at hz
        simp only [Set.mem_ofPred_eq] at hz
        linarith
      refine Filter.Frequently.filter_mono ?_ hle
      refine Filter.Eventually.frequently ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hHr z hz
    · filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds h0'] with z hz
      exact hHr z hz
  have hHo : analyticOrderAt H ρ = analyticOrderAt G ρ :=
    analyticOrderAt_eq_of_eventuallyEq_mul hHf hua hu0 (hGd.analyticAt ρ)
  refine ⟨?_, hHo.trans hGo⟩
  rw [hHf.eq_of_nhds, hGF ρ hρ1]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hu0
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (pow_ne_zero _ (sub_ne_zero.2 hρ1))
      · exact h
  · intro h; rw [h]; simp

/-- **The zeros of the completed function lie in the critical strip** `0 ≤ Re s ≤ 1`, given
that `F` does not vanish on `Re s > 1`; moreover `H 2 ≠ 0`. -/
theorem completed_zeros_mem_strip (F G H : ℂ → ℂ) (m : ℕ) (D : FunctionalEquation F)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Gamma (D.α i * s + D.r i)) * G s)
    (hHrefl : ∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s))
    (hFne1 : ∀ s : ℂ, 1 < s.re → F s ≠ 0) :
    (∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) ∧ H 2 ≠ 0 := by
  have hw0 : D.w ≠ 0 := by
    intro h; have := D.norm_w; rw [h, norm_zero] at this; norm_num at this
  have hHne1 : ∀ s : ℂ, 1 < s.re → H s ≠ 0 := by
    intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
    rw [hHr s (by linarith), hGF s hs1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs0)
      ((cpow_ne_zero_iff_of_exponent_ne_zero hs0).mpr hQ0))
      (Finset.prod_ne_zero_iff.2 fun i _ => Gamma_ne_zero_of_re_pos ?_))
      (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hs1)) (hFne1 s hs))
    simp only [add_re, re_ofReal_mul]
    have := D.α_pos i; have := D.r_re_nonneg i; nlinarith
  refine ⟨fun s h0 => ?_, hHne1 2 (by norm_num)⟩
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hlt | hgt
  · have hre : 1 < (1 - starRingEnd ℂ s).re := by simp; linarith
    have := hHrefl (1 - starRingEnd ℂ s)
    simp only [map_sub, map_one, conj_conj, sub_sub_cancel] at this
    rw [h0] at this
    exact mul_ne_zero hw0 ((map_ne_zero _).2 (hHne1 _ hre)) this.symm
  · exact hHne1 s hgt h0

/-- **The exceptional set.** There is a finite set `X` (contained in `Re s ≤ 1`) and a height
`TX ≥ 0` such that outside `X` the zeros of `F` and of the completed function `H` on `Re s ≥ 0`
agree with multiplicity, and every zero of `H` with `|Im ρ| > TX` is a zero of `G` of the same
order. -/
theorem exists_finset_completed_zeros_eq (F G H : ℂ → ℂ) (m : ℕ) (D : FunctionalEquation F)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (hGd : Differentiable ℂ G)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Gamma (D.α i * s + D.r i)) * G s)
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) :
    ∃ X : Finset ℂ, ∃ TX : ℝ, 0 ≤ TX ∧ (∀ x ∈ X, x.re ≤ 1) ∧
      (∀ ρ : ℂ, 0 ≤ ρ.re → ρ ∉ X →
        ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ)) ∧
      (∀ ρ, H ρ = 0 → TX < |ρ.im| →
        G ρ = 0 ∧ analyticOrderNatAt H ρ = analyticOrderNatAt G ρ) := by
  classical
  set X : Finset ℂ := insert 0 (insert 1 (Finset.univ.image fun i => -D.r i / (D.α i : ℂ)))
    with hX
  set TX : ℝ := ∑ x ∈ X, |x.im| with hTXdef
  have hXim : ∀ x ∈ X, |x.im| ≤ TX := fun x hx =>
    Finset.single_le_sum (f := fun x : ℂ => |x.im|) (fun _ _ => abs_nonneg _) hx
  have hTX0 : 0 ≤ TX := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hXre : ∀ x ∈ X, x.re ≤ 1 := by
    intro x hx
    simp only [X, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨i, rfl⟩
    · simp
    · simp
    · have hα := D.α_pos i
      have hr := D.r_re_nonneg i
      have : (-D.r i / (D.α i : ℂ)).re = -(D.r i).re / D.α i := by
        rw [div_ofReal_re]; simp
      rw [this]
      have : -(D.r i).re / D.α i ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hα.le
      linarith
  have heqFH : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ∉ X →
      ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ) := by
    intro ρ hρ hρX
    have hρ0 : ρ ≠ 0 := fun h => hρX (by rw [h, hX]; exact Finset.mem_insert_self _ _)
    have hρ1 : ρ ≠ 1 := fun h => hρX (by
      rw [h, hX]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hpole : ∀ i, (D.α i : ℂ) * ρ + D.r i ≠ 0 := by
      intro i h
      apply hρX
      have hα : (D.α i : ℂ) ≠ 0 := by exact_mod_cast (D.α_pos i).ne'
      have : ρ = -D.r i / (D.α i : ℂ) := by field_simp; linear_combination h
      rw [this, hX]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    obtain ⟨h1, h2⟩ := completed_eq_zero_iff_and_analyticOrderAt_eq F G H m hFd hGd hGF D hHd
      hHr ρ hρ hρ0 hρ1 hpole
    exact ⟨h1.symm, by simp only [analyticOrderNatAt, h2]⟩
  refine ⟨X, TX, hTX0, hXre, heqFH, fun ρ h0 hT => ?_⟩
  have hρX : ρ ∉ X := fun h => by have := hXim ρ h; linarith
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hT; linarith
  obtain ⟨hFH, hord⟩ := heqFH ρ (hstrip ρ h0).1 hρX
  have hF0 : F ρ = 0 := hFH.2 h0
  have hev : G =ᶠ[nhds ρ] fun w => (w - 1) ^ m * F w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ1] with w hw
    exact hGF w hw
  have hGo := analyticOrderAt_eq_of_eventuallyEq_mul hev
    ((analyticAt_id.sub analyticAt_const).pow m)
    (pow_ne_zero _ (sub_ne_zero.2 hρ1))
    (hFd.analyticAt (isOpen_compl_singleton.mem_nhds hρ1))
  refine ⟨by rw [hGF ρ hρ1, hF0, mul_zero], ?_⟩
  rw [← hord]
  simp only [analyticOrderNatAt, hGo]

/-- **Finiteness of the zero sets.** If the completed function `H` is entire, not identically
zero, with its zeros in the critical strip, and its zeros agree with those of `F` on `Re s ≥ 0`
outside a finite set, then the zeros of `H` and `F` up to any height are finite in number. -/
theorem finite_zeros_of_completed (F H : ℂ → ℂ) (X : Finset ℂ) (hHd : Differentiable ℂ H)
    (hH2 : H 2 ≠ 0) (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
    (heqFH : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ∉ X →
      ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ)) :
    (∀ T : ℝ, {ρ | H ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite) ∧
    (∀ T : ℝ, {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite) ∧
    (∀ T : ℝ, {ρ | H ρ = 0 ∧ |ρ.im| ≤ T}.Finite) := by
  have hfinHT : ∀ T : ℝ, {ρ | H ρ = 0 ∧ |ρ.im| ≤ T}.Finite := by
    intro T
    refine (Complex.finite_setOf_eq_zero_norm_le hHd hH2 (1 + |T|)).subset
      fun ρ hρ => ⟨hρ.1, ?_⟩
    have := norm_le_abs_re_add_abs_im ρ
    obtain ⟨r0, r1⟩ := hstrip ρ hρ.1
    rw [abs_of_nonneg r0] at this
    have := le_abs_self T
    linarith [hρ.2]
  have hfinHS : ∀ T : ℝ, {ρ | H ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite :=
    fun T => (hfinHT T).subset fun ρ hρ => ⟨hρ.1, hρ.2.2⟩
  refine ⟨hfinHS, fun T => ?_, hfinHT⟩
  refine ((hfinHS T).union X.finite_toSet).subset fun ρ hρ => ?_
  by_cases hρX : ρ ∈ X
  · exact Or.inr hρX
  · exact Or.inl ⟨(heqFH ρ hρ.2.1 hρX).1.1 hρ.1, hρ.2⟩

end SelbergClass
