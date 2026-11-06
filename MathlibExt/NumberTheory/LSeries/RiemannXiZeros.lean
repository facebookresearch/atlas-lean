/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXiHadamard
import MathlibExt.Analysis.Complex.HadamardFactorization
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# The zeros of `ξ` and the nontrivial zeros of `ζ`

API relating the zeros of the Riemann xi function `RiemannXi.riemannXi` to those of `ζ`, and for
families listing the zeros of `ξ` with multiplicity, that is, `z : ι → ℂ` with
`∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w`. Such families are the index sets
of sums "over the nontrivial zeros `ρ` of `ζ`, counted with multiplicity".

## Main statements

* `RiemannXi.riemannZeta_eq_riemannXi_mul_div`: `ζ(s) = 2 ξ(s) π^{s/2} / (Γ(s/2) s (s - 1))`.
* `RiemannXi.analyticOrderAt_riemannXi_one_sub`: `ξ` has the same order at `w` and `1 - w`.
* `RiemannXi.logDeriv_riemannXi_eq`: `ξ'/ξ(s) = ζ'/ζ(s) + 1/(s - 1) - (log π)/2 + ψ(s/2 + 1)/2`,
  and `RiemannXi.logDeriv_riemannXi_one_sub`: `ξ'/ξ(1 - s) = -ξ'/ξ(s)`.
* `RiemannXi.exists_riemannZeta_eventually_eq_zpow_mul`: near a nontrivial zero `p`,
  `ζ(s) = (s - p) ^ m E(s)` with `m` the order of `ξ` at `p` and `E(p) ≠ 0`.
* `RiemannXi.exists_card_eq_analyticOrderAt`: a family listing the zeros of `ξ` with
  multiplicity exists.
* `RiemannXi.mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt`,
  `RiemannXi.exists_eq_of_card_eq_analyticOrderAt`,
  `RiemannXi.finite_setOf_abs_im_le_of_card_eq_analyticOrderAt`: such a family lists exactly
  the nontrivial zeros, and only finitely many indices lie below any height.
* `exists_eq_neg_two_mul_of_riemannZeta_eq_zero_of_re_neg`: the zeros of `ζ` with `Re s < 0` are
  the trivial zeros `-2n`.
* `finite_setOf_mem_riemannZetaNontrivialZeros_abs_im_sub_le`: finitely many nontrivial zeros
  lie in any horizontal strip.
* `Complex.analyticOrderAt_inv_Gamma_neg_natCast`: `1 / Γ` has a simple zero at each `-n`.
-/

@[expose] public section

open Filter Topology Set ComplexConjugate

namespace Complex

/-- `1 / Γ` vanishes to order exactly one at each non-positive integer `-n`. -/
theorem analyticOrderAt_inv_Gamma_neg_natCast (n : ℕ) :
    analyticOrderAt (fun s : ℂ => (Gamma s)⁻¹) (-(n : ℂ)) = 1 := by
  set f : ℂ → ℂ := fun s => (Gamma s)⁻¹ with hf_def
  have hfan : ∀ w, AnalyticAt ℂ f w := fun w => differentiable_one_div_Gamma.analyticAt w
  have hrec : ∀ s, f s = s * f (s + 1) := by
    intro s
    by_cases hs : s = 0
    · simp [hf_def, hs, Gamma_zero]
    · simp only [hf_def, Gamma_add_one s hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have hid : ∀ w : ℂ, analyticOrderAt (fun s : ℂ => s) w = analyticOrderAt (· - (0 : ℂ)) w := by
    intro w; congr 1; funext s; exact (sub_zero s).symm
  have hstep : ∀ w, analyticOrderAt f w =
      analyticOrderAt (fun s : ℂ => s) w + analyticOrderAt f (w + 1) := by
    intro w
    have hfeq : f = (fun s : ℂ => s) * (f ∘ (fun s => s + 1)) := by
      funext s; simp only [Pi.mul_apply, Function.comp_apply]; exact hrec s
    have hg : AnalyticAt ℂ (fun s : ℂ => s + 1) w := by fun_prop
    have hcomp : analyticOrderAt (f ∘ (fun s => s + 1)) w = analyticOrderAt f (w + 1) :=
      analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)
    rw [← hcomp]
    conv_lhs => rw [hfeq]
    exact analyticOrderAt_mul (by fun_prop) ((hfan _).comp hg)
  induction n with
  | zero =>
    rw [hstep, hid, Nat.cast_zero, neg_zero, analyticOrderAt_id_sub_const_self, zero_add,
      (hfan _).analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gamma_ne_zero fun m h => by
        have := congrArg re h
        simp at this
        linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])), add_zero]
  | succ n ih =>
    rw [hstep, hid, analyticOrderAt_id_sub_const_of_ne (by
      intro h
      have := congrArg re h
      simp at this
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]), zero_add]
    convert ih using 2
    push_cast; ring

end Complex

/-- A nontrivial zero of `ζ` is nonzero. -/
theorem ne_zero_of_mem_riemannZetaNontrivialZeros {ρ : ℂ} (hρ : ρ ∈ riemannZetaNontrivialZeros) :
    ρ ≠ 0 := by
  rintro rfl
  have := hρ.1
  rw [riemannZeta_zero] at this
  norm_num at this

/-- A nontrivial zero of `ζ` is not `1`. -/
theorem ne_one_of_mem_riemannZetaNontrivialZeros {ρ : ℂ} (hρ : ρ ∈ riemannZetaNontrivialZeros) :
    ρ ≠ 1 := by
  rintro rfl
  exact riemannZeta_ne_zero_of_one_le_re (by simp) hρ.1

/-- The nontrivial zeros of `ζ` are symmetric under `ρ ↦ 1 - ρ`. -/
theorem one_sub_mem_riemannZetaNontrivialZeros {ρ : ℂ} (hρ : ρ ∈ riemannZetaNontrivialZeros) :
    1 - ρ ∈ riemannZetaNontrivialZeros := by
  rw [← RiemannXi.riemannXi_eq_zero_iff, RiemannXi.riemannXi_one_sub,
    RiemannXi.riemannXi_eq_zero_iff]
  exact hρ

/-- The nontrivial zeros of `ζ` are symmetric under complex conjugation. -/
theorem conj_mem_riemannZetaNontrivialZeros {ρ : ℂ} (hρ : ρ ∈ riemannZetaNontrivialZeros) :
    conj ρ ∈ riemannZetaNontrivialZeros := by
  obtain ⟨h0, h1, h2⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h0, map_zero]
  · simpa using h1
  · simpa using h2

/-- The zeros of `ζ` in the left half-plane are the trivial zeros `-2n`, `n ≥ 1`. -/
theorem exists_eq_neg_two_mul_of_riemannZeta_eq_zero_of_re_neg {s : ℂ} (hs : s.re < 0)
    (hζ : riemannZeta s = 0) : ∃ n : ℕ, 0 < n ∧ s = -(2 * (n : ℂ)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    rw [← completedRiemannZeta_one_sub] at h
    have h2 := riemannZeta_def_of_ne_zero h1s
    rw [h, zero_div] at h2
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) h2
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hζ
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp (hζ.resolve_left hΛ)
  refine ⟨n, ?_, hn⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact absurd (by simpa using hn) hs0
  · exact h

/-- Only finitely many nontrivial zeros of `ζ` lie in the horizontal strip `|Im ρ - R| ≤ h`. -/
theorem finite_setOf_mem_riemannZetaNontrivialZeros_abs_im_sub_le (R h : ℝ) :
    {ρ : ℂ | ρ ∈ riemannZetaNontrivialZeros ∧ |ρ.im - R| ≤ h}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + |h| + |R|)).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨hρ, h2⟩
  refine ⟨?_, hρ.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1 + |h| + |R| := by
      have hre : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hρ.2.1, hρ.2.2]
      have him : |ρ.im| ≤ |h| + |R| := by
        have := abs_sub_abs_le_abs_sub ρ.im R
        linarith [le_abs_self h]
      linarith

namespace RiemannXi

/-- `ξ(0) ≠ 0`. -/
theorem riemannXi_zero_ne_zero : riemannXi 0 ≠ 0 := by simp [riemannXi_zero]

/-- `ξ` is not identically zero near any point: its orders of vanishing are finite. -/
theorem analyticOrderAt_riemannXi_ne_top (w : ℂ) : analyticOrderAt riemannXi w ≠ ⊤ :=
  Complex.analyticOrderAt_ne_top_of_differentiable differentiable_riemannXi
    riemannXi_zero_ne_zero w

/-- `ξ` vanishes to the same order at `w` and at `1 - w`. -/
theorem analyticOrderAt_riemannXi_one_sub (w : ℂ) :
    analyticOrderAt riemannXi (1 - w) = analyticOrderAt riemannXi w := by
  set m := (analyticOrderAt riemannXi w).toNat with hm
  have hmw : analyticOrderAt riemannXi w = m :=
    (ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top w)).symm
  obtain ⟨g, hga, hg0, hge⟩ :=
    (differentiable_riemannXi.analyticAt w).analyticOrderAt_eq_natCast.mp hmw
  rw [hmw]
  refine (differentiable_riemannXi.analyticAt (1 - w)).analyticOrderAt_eq_natCast.mpr
    ⟨fun z => (-1) ^ m * g (1 - z), ?_, ?_, ?_⟩
  · have hc : AnalyticAt ℂ (fun z : ℂ => 1 - z) (1 - w) := by fun_prop
    have hg' : AnalyticAt ℂ g ((fun z : ℂ => 1 - z) (1 - w)) := by simpa using hga
    exact analyticAt_const.mul (hg'.comp hc)
  · simp [hg0]
  · have ht : Tendsto (fun z : ℂ => 1 - z) (𝓝 (1 - w)) (𝓝 w) := by
      have hc : Continuous fun z : ℂ => 1 - z := by fun_prop
      simpa using hc.tendsto (1 - w)
    filter_upwards [ht.eventually hge] with z hz
    rw [← riemannXi_one_sub z, hz, smul_eq_mul, smul_eq_mul,
      show (1 - z - w) = (-1) * (z - (1 - w)) by ring, mul_pow]
    ring

/-- `ζ(s) = 2 ξ(s) π^{s/2} Γ(s/2)⁻¹ / (s (s - 1))` for `s ≠ 0, 1`. -/
theorem riemannZeta_eq_riemannXi_mul_div {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannZeta s = 2 * riemannXi s * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ /
      (s * (s - 1)) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hxi : riemannXi s = 1 / 2 * (s * (s - 1)) * completedRiemannZeta s := by
    rw [riemannXi_eq_mul_completedRiemannZeta h0 h1]; ring
  have hpi : (Real.pi : ℂ) ^ (s / 2) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simpa using h0)).mpr
      (by exact_mod_cast Real.pi_ne_zero)
  rw [riemannZeta_def_of_ne_zero h0, Complex.Gammaℝ_def, hxi, neg_div, Complex.cpow_neg,
    div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

/-- Off the real axis, a zero of `ζ` is a zero of `ξ`. -/
theorem riemannXi_eq_zero_of_riemannZeta_eq_zero {s : ℂ} (him : s.im ≠ 0)
    (hζ : riemannZeta s = 0) : riemannXi s = 0 := by
  have h0 : s ≠ 0 := fun h => him (by rw [h]; simp)
  have h1 : s ≠ 1 := fun h => him (by rw [h]; simp)
  have hpi : (Real.pi : ℂ) ^ (s / 2) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simpa using h0)).mpr
      (by exact_mod_cast Real.pi_ne_zero)
  have hG : (Complex.Gamma (s / 2))⁻¹ ≠ 0 := by
    refine inv_ne_zero (Complex.Gamma_ne_zero fun m hm => him ?_)
    have := congrArg Complex.im hm
    simp at this
    linarith
  rw [riemannZeta_eq_riemannXi_mul_div h0 h1, div_eq_zero_iff] at hζ
  rcases hζ with hζ | hζ
  · simpa [hpi, hG] using hζ
  · exact absurd hζ (mul_ne_zero h0 (sub_ne_zero.mpr h1))

/-- The functional equation for `ξ'`: `ξ'(1 - s) = -ξ'(s)`. -/
theorem deriv_riemannXi_one_sub (s : ℂ) : deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have h : riemannXi = fun s => riemannXi (1 - s) := funext fun s => (riemannXi_one_sub s).symm
  have := deriv_comp_const_sub (f := riemannXi) (a := 1) (x := s)
  rw [← h] at this
  rw [this]; ring

/-- The functional equation for `ξ'/ξ`: `ξ'/ξ(1 - s) = -ξ'/ξ(s)`. -/
theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub]
  ring

/-- `ξ(s) ≠ 0` wherever `s ≠ 1` and `ζ(s) ≠ 0`. -/
theorem riemannXi_ne_zero_of_riemannZeta_ne_zero {s : ℂ} (hs1 : s ≠ 1)
    (hs : riemannZeta s ≠ 0) : riemannXi s ≠ 0 := by
  intro h
  rcases eq_or_ne s 0 with rfl | h0
  · exact riemannXi_zero_ne_zero h
  · exact hs (by rw [riemannZeta_eq_riemannXi_mul_div h0 hs1, h]; simp)

/-- **The logarithmic derivative of `ξ`**: `ξ'/ξ = ζ'/ζ + 1/(s-1) - (log π)/2 + ψ(s/2+1)/2`
wherever `s ≠ 1` and `ζ(s) ≠ 0`. -/
theorem logDeriv_riemannXi_eq {s : ℂ} (hs1 : s ≠ 1) (hs : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = logDeriv riemannZeta s +
      (1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2) := by
  set D : ℂ → ℂ := fun w => (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)
    with hD
  have hζ : ∀ w, w ≠ 1 → riemannZeta w = riemannXi w / D w := by
    intro w hw1
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hD, riemannZeta_zero]
      norm_num
    · have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
      have hG : Complex.Gamma (w / 2 + 1) = w / 2 * Complex.Gamma (w / 2) :=
        Complex.Gamma_add_one _ (div_ne_zero hw0 two_ne_zero)
      have hDw : D w = (w * (w - 1) / 2) * Complex.Gammaℝ w := by
        simp only [hD, hG, Complex.Gammaℝ_def]; ring
      rw [riemannZeta_def_of_ne_zero hw0, hDw, riemannXi_eq_mul_completedRiemannZeta hw0 hw1,
        mul_div_mul_left _ _ (div_ne_zero (mul_ne_zero hw0 hw1') two_ne_zero)]
  have hGs : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m hm
    apply hs
    have : s = -2 * ((m : ℂ) + 1) := by linear_combination 2 * hm
    rw [this]; exact riemannZeta_neg_two_mul_nat_add_one m
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDs : D s ≠ 0 := by
    simp only [hD]
    refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) ?_) (Complex.Gamma_ne_zero hGs)
    simp [Complex.cpow_eq_zero_iff, hpi]
  have hxis : riemannXi s ≠ 0 := riemannXi_ne_zero_of_riemannZeta_ne_zero hs1 hs
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s :=
    (Complex.differentiableAt_Gamma _ hGs).comp s (by fun_prop)
  have hcd : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact h1.const_cpow (Or.inl hpi)
  have hDd : DifferentiableAt ℂ D s :=
    ((differentiableAt_id.sub_const 1).mul hcd.differentiableAt).mul hΓ
  have hev : riemannZeta =ᶠ[𝓝 s] fun w => riemannXi w / D w := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with w hw using hζ w hw
  have hL1 : logDeriv riemannZeta s = logDeriv riemannXi s - logDeriv D s := by
    rw [← logDeriv_fun_div s hxis hDs (differentiable_riemannXi s) hDd, logDeriv_apply,
      logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hL2 : logDeriv D s =
      1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2 := by
    have hc0 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
    rw [show D = fun w => (fun w : ℂ => (w - 1) * (Real.pi : ℂ) ^ (-w / 2)) w *
        (fun w : ℂ => Complex.Gamma (w / 2 + 1)) w from rfl,
      logDeriv_fun_mul (f := fun w : ℂ => (w - 1) * (Real.pi : ℂ) ^ (-w / 2))
        (g := fun w : ℂ => Complex.Gamma (w / 2 + 1)) s
        (mul_ne_zero (sub_ne_zero.mpr hs1) hc0) (Complex.Gamma_ne_zero hGs)
        ((differentiableAt_id.sub_const 1).mul hcd.differentiableAt) hΓ,
      logDeriv_fun_mul (f := fun w : ℂ => w - 1) (g := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s
        (sub_ne_zero.mpr hs1) hc0 (differentiableAt_id.sub_const 1) hcd.differentiableAt]
    have e1 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]; simp
    have e2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s =
        -(Real.log Real.pi : ℂ) / 2 := by
      rw [logDeriv_apply, hcd.deriv, ← Complex.ofReal_log Real.pi_pos.le]
      field_simp
    have e3 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s =
        Complex.digamma (s / 2 + 1) / 2 := by
      have hg : HasDerivAt (fun w : ℂ => w / 2 + 1) (1 / 2) s := by
        simpa using ((hasDerivAt_id s).div_const 2).add_const 1
      rw [show (fun w : ℂ => Complex.Gamma (w / 2 + 1)) =
          Complex.Gamma ∘ (fun w : ℂ => w / 2 + 1) from rfl,
        logDeriv_comp (g := fun w : ℂ => w / 2 + 1) (Complex.differentiableAt_Gamma _ hGs)
          hg.differentiableAt, hg.deriv, Complex.digamma_def]
      ring
    rw [e1, e2, e3]; ring
  rw [hL1, hL2]; ring

/-- **Local factorisation of `ζ` at a nontrivial zero.** If `ξ` vanishes to order `m` at a
nontrivial zero `p` of `ζ`, then `ζ(s) = (s - p) ^ m E(s)` near `p` with `E` analytic and nonzero
at `p`. -/
theorem exists_riemannZeta_eventually_eq_zpow_mul {p : ℂ}
    (hp : p ∈ riemannZetaNontrivialZeros) {m : ℕ} (hm : analyticOrderAt riemannXi p = m) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E p ∧ E p ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] p, riemannZeta s = (s - p) ^ (m : ℤ) * E s := by
  have hpih : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) s := fun s =>
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have hpic : ∀ s : ℂ, (Real.pi : ℂ) ^ s ≠ 0 := by
    intro s
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => Real.pi_ne_zero (by exact_mod_cast h.1)
  have hp0 := ne_zero_of_mem_riemannZetaNontrivialZeros hp
  have hp1 := ne_one_of_mem_riemannZetaNontrivialZeros hp
  obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ :=
    (differentiable_riemannXi.analyticAt p).analyticOrderAt_eq_natCast.mp hm
  let E : ℂ → ℂ := fun s =>
    2 * ξ₁ s * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ / (s * (s - 1))
  have hE : AnalyticAt ℂ E p := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (show p ∈ ({0}ᶜ : Set ℂ) from hp0),
      isOpen_compl_singleton.mem_nhds (show p ∈ ({1}ᶜ : Set ℂ) from hp1),
      hξ₁a.eventually_analyticAt] with s hs0 hs1 hsa
    have h2' : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma (s / 2))⁻¹) s :=
      (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const (2 : ℂ))) s
    have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
    exact (((hsa.differentiableAt.const_mul 2).mul (hpih s)).mul h2').div (by fun_prop) hden
  have hE0 : E p ≠ 0 := by
    have hG : Complex.Gamma (p / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun n hn => hp0 ?_
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (n : ℝ) = 0 := by linarith [hp.2.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have : p / 2 = 0 := by rw [hn]; simp [show (n : ℂ) = 0 by exact_mod_cast hn0]
      simpa using this
    have hden : p * (p - 1) ≠ 0 := mul_ne_zero hp0 (sub_ne_zero.mpr hp1)
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hξ₁0)
      (hpic _)) (inv_ne_zero hG)) hden
  refine ⟨E, hE, hE0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
      (show p ∈ ({0}ᶜ : Set ℂ) from hp0)),
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (show p ∈ ({1}ᶜ : Set ℂ) from hp1)),
    nhdsWithin_le_nhds hξ₁e] with s hs0 hs1 hse
  rw [riemannZeta_eq_riemannXi_mul_div hs0 hs1, hse, zpow_natCast, smul_eq_mul]
  simp only [E]
  ring

/-! ### Families listing the zeros of `ξ` with multiplicity -/

section Family

variable {ι : Type*} {z : ι → ℂ}

/-- A family listing the zeros of `ξ` with multiplicity consists of nontrivial zeros of `ζ`. -/
theorem mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (n : ι) :
    z n ∈ riemannZetaNontrivialZeros :=
  (riemannXi_eq_zero_iff _).mp (Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz n)

/-- A family listing the zeros of `ξ` with multiplicity lists every nontrivial zero of `ζ`. -/
theorem exists_eq_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) {ρ : ℂ}
    (hρ : ρ ∈ riemannZetaNontrivialZeros) : ∃ n, z n = ρ := by
  have h0 : analyticOrderAt riemannXi ρ ≠ 0 := fun h =>
    ((differentiable_riemannXi.analyticAt ρ).analyticOrderAt_eq_zero.mp h)
      ((riemannXi_eq_zero_iff ρ).mpr hρ)
  rw [← hz] at h0
  obtain ⟨⟨n, hn⟩⟩ := (ENat.card_ne_zero_iff_nonempty _).mp h0
  exact ⟨n, hn⟩

/-- In a family listing the zeros of `ξ` with multiplicity, each zero is listed finitely often. -/
theorem finite_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (p : ℂ) :
    Finite {n // z n = p} :=
  ENat.card_lt_top.mp (by rw [hz]; exact lt_top_iff_ne_top.mpr (analyticOrderAt_riemannXi_ne_top p))

/-- The reflection `1 - z` of a family listing the zeros of `ξ` with multiplicity is again such a
family. -/
theorem card_one_sub_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (w : ℂ) :
    ENat.card {n // 1 - z n = w} = analyticOrderAt riemannXi w := by
  rw [← analyticOrderAt_riemannXi_one_sub w, ← hz]
  exact ENat.card_congr (Equiv.subtypeEquivRight fun n => by
    constructor <;> intro h <;> linear_combination -h)

/-- In a family listing the zeros of `ξ` with multiplicity, only finitely many indices have
`|Im z n| ≤ R`. -/
theorem finite_setOf_abs_im_le_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (R : ℝ) :
    {n | |(z n).im| ≤ R}.Finite := by
  have hfin : {ρ : ℂ | ρ ∈ riemannZetaNontrivialZeros ∧ |ρ.im| ≤ R}.Finite :=
    (finite_setOf_mem_riemannZetaNontrivialZeros_abs_im_sub_le 0 R).subset fun ρ hρ =>
      ⟨hρ.1, by simpa using hρ.2⟩
  refine (hfin.biUnion fun p _ =>
    (Set.finite_coe_iff.mp (finite_of_card_eq_analyticOrderAt hz p) :
      {n | z n = p}.Finite)).subset ?_
  intro n hn
  simp only [mem_iUnion]
  exact ⟨z n, ⟨mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz n, hn⟩, rfl⟩

/-- In a family listing the zeros of `ξ` with multiplicity, only finitely many indices have
`|Im z n| < R`. -/
theorem finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (R : ℝ) :
    {n | |(z n).im| < R}.Finite :=
  (finite_setOf_abs_im_le_of_card_eq_analyticOrderAt hz R).subset fun _ hn =>
    le_of_lt (show _ < R from hn)

end Family

/-- **A family listing the zeros of `ξ` with multiplicity**, i.e. the nontrivial zeros of `ζ`,
each listed as often as its multiplicity. -/
theorem exists_card_eq_analyticOrderAt :
    ∃ (ι : Type) (z : ι → ℂ), ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w :=
  ⟨Σ w : ℂ, Fin (analyticOrderAt riemannXi w).toNat, Sigma.fst,
    Complex.card_sigma_fin_analyticOrderAt differentiable_riemannXi riemannXi_zero_ne_zero⟩

end RiemannXi
