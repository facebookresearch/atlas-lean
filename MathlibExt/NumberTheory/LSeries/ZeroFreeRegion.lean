/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXiHadamard
public import MathlibExt.NumberTheory.LSeries.DirichletLogDeriv
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Zero-free regions for `ζ` and for real Dirichlet `L`-functions

We bound `-Re ζ'/ζ` near the line `Re s = 1` through the zero-sum expansion coming from the
Hadamard product of `ξ`, and prove the de la Vallée Poussin type statements for real characters:
for an absolute constant `c > 0` and every real nonprincipal Dirichlet character `χ` modulo `q`,
`L(s, χ)` has at most one zero, counted with multiplicity, in the region
`Re s > 1 - c / log (q (|Im s| + 2))`; such a zero is real and simple.

## Main statements

* `exists_neg_re_logDeriv_riemannZeta_lt_one_div_sub_one_add`:
  `-ζ'/ζ(σ) < 1 / (σ - 1) + A` for `1 < σ ≤ 2`.
* `Complex.re_one_div_sub_add_one_div_nonneg`: `Re (1 / (s - ρ) + 1 / ρ) ≥ 0` for
  `0 ≤ Re ρ ≤ 1 ≤ Re s`.
* `exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum`:
  `-Re ζ'/ζ(s) < A log |t| - ∑_ρ Re (1 / (s - ρ) + 1 / ρ)` for `1 ≤ σ ≤ 2`, `|t| ≥ 2`.
* `exists_neg_re_logDeriv_riemannZeta_lt_log`: `-Re ζ'/ζ(s) < A log |t|` there.
* `exists_neg_re_logDeriv_riemannZeta_lt_log_sub_one_div`:
  `-Re ζ'/ζ(σ + iγ) < A log |γ| - 1 / (σ - β)` at a nontrivial zero `β + iγ`.
* `exists_neg_re_logDeriv_riemannZeta_lt_re_one_div_sub_one_add_log`:
  `-Re ζ'/ζ(s) < Re (1 / (s - 1)) + c log (|t| + 2)` for `σ > 1`.
* `lt_one_sub_div_of_forall_div_sub_lt`: the optimisation step of the zero-free region argument.
* `DirichletCharacter.LFunction_ne_zero_of_sq_eq_one_of_abs_im_gt`: a real nonprincipal
  `L(s, χ)` has no zeros with `σ > 1 - δ / (4 log (q (|t| + 2)))` and `|t| > δ / log q`.
* `DirichletCharacter.sum_le_one_of_sq_eq_one`: the zeros of a real nonprincipal `L(s, χ)` in the
  region, counted with multiplicity, number at most one.
* `DirichletCharacter.LFunction_zeros_subsingleton_of_sq_eq_one`,
  `DirichletCharacter.im_eq_zero_of_LFunction_eq_zero_of_sq_eq_one`,
  `DirichletCharacter.analyticOrderAt_LFunction_eq_one_of_sq_eq_one`: there is at most one zero in
  the region, and it is real and simple.
-/

@[expose] public section

open Filter Topology

/-! ### The Riemann zeta function -/

/-- There is a constant `A` with `-ζ'(σ)/ζ(σ) < 1 / (σ - 1) + A` for `1 < σ ≤ 2`. Since
`ζ'(σ)/ζ(σ)` is real for real `σ > 1`, its real part is its value. -/
theorem exists_neg_re_logDeriv_riemannZeta_lt_one_div_sub_one_add :
    ∃ A : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re < 1 / (σ - 1) + A := by
  -- `riemannZeta₁ σ = (σ - 1) ζ(σ)` does not vanish on `[1, 2]`
  have hne : ∀ σ : ℝ, 1 ≤ σ → riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ with h | h
    · subst h; simp
    · have hs : (σ : ℂ) ≠ 1 := by exact_mod_cast h.ne'
      have hz := riemannZeta_ne_zero_of_one_le_re (s := (σ : ℂ)) (by simpa using hσ)
      rw [riemannZeta_eq_inv_sub_mul hs] at hz
      exact right_ne_zero_of_mul hz
  set F : ℝ → ℂ := fun σ => deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ) with hF
  have hcont : ContinuousOn F (Set.Icc 1 2) := by
    intro σ hσ
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · exact (differentiable_riemannZeta₁.deriv.continuous.comp
        Complex.continuous_ofReal).continuousAt
    · exact (differentiable_riemannZeta₁.continuous.comp Complex.continuous_ofReal).continuousAt
    · exact hne σ hσ.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨B + 1, fun σ h1 h2 => ?_⟩
  have hs : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne'
  have hid : deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) = -((σ : ℂ) - 1)⁻¹ + F σ := by
    rw [hF, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
    have := hne σ h1.le
    have : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp
  have hFb := hB σ ⟨h1.le, h2⟩
  have hre : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re,
      one_div]
  rw [hid, Complex.add_re, Complex.neg_re, hre]
  have : -(F σ).re ≤ B := by linarith [Complex.abs_re_le_norm (F σ), neg_abs_le (F σ).re]
  linarith

/-- **Positivity of the zero terms.** For `ρ` with `0 ≤ Re ρ ≤ 1` (for instance a nontrivial zero
of `ζ`) and `Re s ≥ 1`, `Re (1 / (s - ρ) + 1 / ρ) ≥ 0`. -/
theorem Complex.re_one_div_sub_add_one_div_nonneg {s ρ : ℂ} (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1)
    (hs : 1 ≤ s.re) : 0 ≤ (1 / (s - ρ) + 1 / ρ).re := by
  rw [Complex.add_re, one_div, one_div, Complex.inv_re, Complex.inv_re, Complex.sub_re]
  exact add_nonneg (div_nonneg (by linarith) (Complex.normSq_nonneg _))
    (div_nonneg hρ₀ (Complex.normSq_nonneg _))

open RiemannXi in
/-- **The zero-sum bound for `-Re ζ'/ζ`.** There is an absolute constant `A` such that for
`s = σ + it` with `1 ≤ σ ≤ 2` and `|t| ≥ 2`,
`-Re ζ'(s)/ζ(s) < A log |t| - ∑_ρ Re (1 / (s - ρ) + 1 / ρ)`, the sum running over the nontrivial
zeros of `ζ` with multiplicity (any family `z` listing the zeros of `ξ` with multiplicity). -/
theorem exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum :
    ∃ A : ℝ, ∀ {ι : Type*} (z : ι → ℂ),
      (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
      ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
        -(deriv riemannZeta s / riemannZeta s).re
          < A * Real.log |s.im| - ∑' n, (1 / (s - z n) + 1 / z n).re := by
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  set c₀ : ℂ := -1 - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (0 / 2 + 1) / 2
    + logDeriv riemannZeta 0 with hc₀
  set K : ℝ := 1 / 2 + |c₀.re| + |Real.log Real.pi| + |C| + 1 with hK
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K / Real.log 2 + 1, fun {ι} z hz s hσ1 hσ2 ht => ?_⟩
  obtain ⟨A₀, B, hAB⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  -- `B` is the absolute constant `c₀`
  have hB : B = c₀ := by
    have h0 := neg_logDeriv_riemannZeta_eq hz hAB (s := 0) zero_ne_one
      (by rw [riemannZeta_zero]; norm_num)
    have : ∑' n, (1 / (0 - z n) + 1 / z n) = 0 := by
      simp [zero_sub, one_div, inv_neg]
    rw [this] at h0
    rw [hc₀]; linear_combination h0
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at ht; simp at ht; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hσ1
  have hE := neg_logDeriv_riemannZeta_eq hz hAB hs1 hζ
  have hm := Complex.summable_one_div_sub_add_one_div (ne_zero_of_card_eq_analyticOrderAt hz)
    (summable_norm_rpow_neg_two hz) s
  have hre : (∑' n, (1 / (s - z n) + 1 / z n)).re = ∑' n, (1 / (s - z n) + 1 / z n).re :=
    Complex.re_tsum hm
  -- the real part of the expansion
  have hEr := congrArg Complex.re hE
  rw [logDeriv_apply] at hEr
  simp only [Complex.neg_re, Complex.sub_re, hre] at hEr
  rw [Complex.add_re, Complex.sub_re] at hEr
  rw [Complex.sub_re (1 / (s - 1)), Complex.div_ofNat_re, Complex.div_ofNat_re,
    Complex.ofReal_re] at hEr
  rw [hEr]
  -- `Re 1/(s-1) ≤ 1/2`
  have h1 : (1 / (s - 1)).re ≤ 1 / 2 := by
    have hn : 2 ≤ ‖s - 1‖ := by
      calc (2 : ℝ) ≤ |s.im| := ht
        _ = |(s - 1).im| := by simp
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    calc (1 / (s - 1)).re ≤ ‖1 / (s - 1)‖ := Complex.re_le_norm _
      _ = 1 / ‖s - 1‖ := by rw [norm_div, norm_one]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn
  -- the digamma term
  set w : ℂ := s / 2 + 1 with hw
  have hwre : w.re = s.re / 2 + 1 := by simp [hw]
  have hwim : w.im = s.im / 2 := by simp [hw]
  have hw0 : w ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hwre] at this; linarith
  have harg : |Complex.arg w| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hwre]; linarith))
  have hCw := hC w hw0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
  have hwn1 : 1 ≤ ‖w‖ := by
    calc (1 : ℝ) ≤ w.re := by rw [hwre]; linarith
      _ ≤ |w.re| := le_abs_self _
      _ ≤ ‖w‖ := Complex.abs_re_le_norm _
  have hwn2 : ‖w‖ ≤ 2 * |s.im| := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re / 2 + 1) + |s.im| / 2 := by
          rw [hwre, hwim, abs_of_pos (by linarith), abs_div, abs_two]
      _ ≤ 2 * |s.im| := by linarith
  have hlogt : Real.log 2 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) ht
  have hlw : Real.log ‖w‖ ≤ 2 * Real.log |s.im| := by
    calc Real.log ‖w‖ ≤ Real.log (2 * |s.im|) := Real.log_le_log (by linarith) hwn2
      _ = Real.log 2 + Real.log |s.im| := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log |s.im| := by linarith
  have hdg : (Complex.digamma w).re ≤ 2 * Real.log |s.im| + |C| := by
    have h3 : (Complex.digamma w - Complex.log w).re ≤ |C| := by
      calc _ ≤ ‖Complex.digamma w - Complex.log w‖ := Complex.re_le_norm _
        _ ≤ C / ‖w‖ := hCw
        _ ≤ |C| / ‖w‖ := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg _) hwn1
    rw [Complex.sub_re, Complex.log_re] at h3
    linarith
  rw [hB]
  have hKL : K ≤ K / Real.log 2 * Real.log |s.im| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    have : 0 ≤ K := by rw [hK]; positivity
    nlinarith
  have hc := neg_abs_le c₀.re
  have hπ := neg_abs_le (Real.log Real.pi)
  have hCa := abs_nonneg C
  have hπ' := le_abs_self (Real.log Real.pi)
  have hexp : (K / Real.log 2 + 1) * Real.log |s.im|
      = K / Real.log 2 * Real.log |s.im| + Real.log |s.im| := by ring
  rw [hexp]
  linarith

/-- The family `Sigma.fst : (Σ w, Fin (analyticOrderAt ξ w).toNat) → ℂ` lists the nontrivial
zeros of `ζ` with multiplicity. -/
private lemma riemannXi_sigma_enum :
    (∀ w, ENat.card {n : (Σ w : ℂ, Fin (analyticOrderAt RiemannXi.riemannXi w).toNat) //
        n.1 = w} = analyticOrderAt RiemannXi.riemannXi w) ∧
      ∀ n : (Σ w : ℂ, Fin (analyticOrderAt RiemannXi.riemannXi w).toNat),
        n.1 ∈ riemannZetaNontrivialZeros :=
  ⟨Complex.card_sigma_fin_analyticOrderAt RiemannXi.differentiable_riemannXi (w₀ := 0)
      (by simp),
    fun n => (RiemannXi.riemannXi_eq_zero_iff _).mp
      (Complex.apply_fst_eq_zero_of_sigma_fin_analyticOrderAt n)⟩

/-- There is an absolute constant `A` with `-Re ζ'(s)/ζ(s) < A log |t|` for `1 ≤ σ ≤ 2` and
`|t| ≥ 2`. -/
theorem exists_neg_re_logDeriv_riemannZeta_lt_log :
    ∃ A : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      -(deriv riemannZeta s / riemannZeta s).re < A * Real.log |s.im| := by
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum.{0}
  refine ⟨A, fun s hs1 hs2 ht => ?_⟩
  obtain ⟨hz, hzmem⟩ := riemannXi_sigma_enum
  have key := hA _ hz s hs1 hs2 ht
  have hnn : 0 ≤ ∑' n : (Σ w : ℂ, Fin (analyticOrderAt RiemannXi.riemannXi w).toNat),
      (1 / (s - n.1) + 1 / n.1).re :=
    tsum_nonneg fun n => Complex.re_one_div_sub_add_one_div_nonneg (hzmem n).2.1 (hzmem n).2.2 hs1
  linarith

/-- There is an absolute constant `A` such that for every nontrivial zero `ρ = β + iγ` of `ζ` with
`|γ| ≥ 2` and every `1 ≤ σ ≤ 2`, `-Re ζ'/ζ(σ + iγ) < A log |γ| - 1 / (σ - β)`. -/
theorem exists_neg_re_logDeriv_riemannZeta_lt_log_sub_one_div :
    ∃ A : ℝ, ∀ ρ ∈ riemannZetaNontrivialZeros, 2 ≤ |ρ.im| → ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 →
      -(deriv riemannZeta ((σ : ℂ) + ρ.im * Complex.I)
          / riemannZeta ((σ : ℂ) + ρ.im * Complex.I)).re
        < A * Real.log |ρ.im| - 1 / (σ - ρ.re) := by
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum.{0}
  refine ⟨A, fun ρ hρ hγ σ hσ1 hσ2 => ?_⟩
  have hd := RiemannXi.differentiable_riemannXi
  have hX0 : RiemannXi.riemannXi 0 ≠ 0 := by simp
  have hfin := Complex.analyticOrderAt_ne_top_of_differentiable hd hX0
  set N : ℂ → ℕ := fun w => (analyticOrderAt RiemannXi.riemannXi w).toNat with hN
  obtain ⟨hz, hzmem⟩ := riemannXi_sigma_enum
  set s : ℂ := (σ : ℂ) + ρ.im * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = ρ.im := by simp [hs]
  have key := hA _ hz s (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2)
    (by rw [hsim]; exact hγ)
  rw [hsim] at key
  have hm := Complex.summable_one_div_sub_add_one_div
    (RiemannXi.ne_zero_of_card_eq_analyticOrderAt hz) (RiemannXi.summable_norm_rpow_neg_two hz) s
  have hmre := Complex.reCLM.summable hm
  have hnn : ∀ n : (Σ w : ℂ, Fin (N w)), 0 ≤ (1 / (s - n.1) + 1 / n.1).re := fun n =>
    Complex.re_one_div_sub_add_one_div_nonneg (hzmem n).2.1 (hzmem n).2.2
      (by rw [hsre]; exact hσ1)
  -- the index of `ρ`
  have hNρ : 0 < N ρ := by
    have hne : analyticOrderAt RiemannXi.riemannXi ρ ≠ 0 := by
      intro h
      rcases analyticOrderAt_eq_zero.mp h with h | h
      · exact h (hd.analyticAt ρ)
      · exact h ((RiemannXi.riemannXi_eq_zero_iff ρ).mpr hρ)
    rw [hN]
    exact Nat.pos_of_ne_zero (fun h => hne (by
      rw [← ENat.natCast_toNat (hfin ρ)]; simp only at h; rw [h]; rfl))
  let n₀ : Σ w : ℂ, Fin (N w) := ⟨ρ, ⟨0, hNρ⟩⟩
  have hle := hmre.le_tsum n₀ (fun j _ => hnn j)
  have hsρ : s - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hs]
  have hterm : 1 / (σ - ρ.re) ≤ (1 / (s - n₀.1) + 1 / n₀.1).re := by
    change 1 / (σ - ρ.re) ≤ (1 / (s - ρ) + 1 / ρ).re
    rw [hsρ, Complex.add_re, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re,
      Complex.ofReal_one]
    have : 0 ≤ (1 / ρ).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg hρ.2.1 (Complex.normSq_nonneg _)
    linarith
  simp only [Complex.reCLM_apply] at hle
  linarith

/-- There is a constant `c₁ > 0` with `-Re ζ'(s)/ζ(s) < Re (1 / (s - 1)) + c₁ log (|t| + 2)` for
all `s = σ + it` with `σ > 1`. -/
theorem exists_neg_re_logDeriv_riemannZeta_lt_re_one_div_sub_one_add_log :
    ∃ c₁ > 0, ∀ s : ℂ, 1 < s.re →
      -(deriv riemannZeta s / riemannZeta s).re <
        (1 / (s - 1)).re + c₁ * Real.log (|s.im| + 2) := by
  -- `riemannZeta₁ s = (s - 1) ζ(s)` does not vanish on `1 ≤ re s`
  have hne : ∀ s : ℂ, 1 ≤ s.re → riemannZeta₁ s ≠ 0 := by
    intro s hs
    by_cases h : s = 1
    · subst h; simp
    · have hz := riemannZeta_ne_zero_of_one_le_re hs
      rw [riemannZeta_eq_inv_sub_mul h] at hz
      exact right_ne_zero_of_mul hz
  -- the compact part near `s = 1`
  have hKc : IsCompact ({s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 4) :=
    (isCompact_closedBall 0 4).inter_left (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s)
      ({s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 4) :=
    differentiable_riemannZeta₁.deriv.continuous.continuousOn.div
      differentiable_riemannZeta₁.continuous.continuousOn (fun s hs => hne s hs.1)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  -- the strip `1 ≤ σ ≤ 2`, `|t| ≥ 2`
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log
  -- the half-plane `σ ≥ 2`, by the Dirichlet series of `Λ`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re →
      -(deriv riemannZeta s / riemannZeta s).re ≤ C := by
    open ArithmeticFunction LSeries in
    have h2 : LSeriesSummable (fun n => (Λ n : ℂ)) 2 :=
      LSeriesSummable_vonMangoldt (by norm_num)
    refine ⟨∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖, fun s hs => ?_⟩
    have hs1 : 1 < s.re := by linarith
    have hsum : LSeriesSummable (fun n => (Λ n : ℂ)) s := LSeriesSummable_vonMangoldt hs1
    have hnorm2 : Summable fun n => ‖term (fun n => (Λ n : ℂ)) 2 n‖ := summable_norm_iff.mpr h2
    have hnorms : Summable fun n => ‖term (fun n => (Λ n : ℂ)) s n‖ :=
      summable_norm_iff.mpr hsum
    have hval : -(deriv riemannZeta s / riemannZeta s) = LSeries (fun n => (Λ n : ℂ)) s := by
      rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1, neg_div]
    rw [← Complex.neg_re, hval]
    calc (LSeries (fun n => (Λ n : ℂ)) s).re ≤ ‖LSeries (fun n => (Λ n : ℂ)) s‖ :=
          Complex.re_le_norm _
      _ ≤ ∑' n, ‖term (fun n => (Λ n : ℂ)) s n‖ := norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖ :=
          hnorms.tsum_le_tsum (fun n => norm_term_le_of_re_le_re _ (by simpa using hs) n) hnorm2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|A| + (|B| + |C| + 1) / Real.log 2, by positivity, fun s hs => ?_⟩
  have hL2 : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hL0 : 0 ≤ Real.log (|s.im| + 2) := hlog2.le.trans hL2
  have hc : |B| + |C| + 1 ≤ (|B| + |C| + 1) / Real.log 2 * Real.log (|s.im| + 2) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    have : 1 ≤ Real.log (|s.im| + 2) / Real.log 2 := (one_le_div hlog2).mpr hL2
    nlinarith [abs_nonneg B, abs_nonneg C]
  have hAL : 0 ≤ |A| * Real.log (|s.im| + 2) := mul_nonneg (abs_nonneg A) hL0
  have hsub : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hre : 0 < (1 / (s - 1)).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos (by simp; linarith) (Complex.normSq_pos.mpr hsub)
  rcases le_or_gt 2 s.re with h2 | h2
  · have := hC s h2
    nlinarith [le_abs_self C, abs_nonneg B]
  rcases le_or_gt 2 |s.im| with ht | ht
  · have h := hA s hs.le h2.le ht
    have hlt : Real.log |s.im| ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
    have : A * Real.log |s.im| ≤ |A| * Real.log (|s.im| + 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self A) hlog0).trans
        (mul_le_mul_of_nonneg_left hlt (abs_nonneg A))
    nlinarith [abs_nonneg B, abs_nonneg C]
  · have hs1 : s ≠ 1 := fun h => hsub (by rw [h, sub_self])
    have hmem : s ∈ {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 4 := by
      refine ⟨hs.le, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im s
      have : |s.re| < 2 := abs_lt.mpr ⟨by linarith, h2⟩
      linarith
    have hGb := hB s hmem
    have hR := hne s hs.le
    have hid : deriv riemannZeta s / riemannZeta s
        = -(1 / (s - 1)) + deriv riemannZeta₁ s / riemannZeta₁ s := by
      rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
      field_simp
    rw [hid, Complex.add_re, Complex.neg_re]
    have : -(deriv riemannZeta₁ s / riemannZeta₁ s).re ≤ |B| := by
      linarith [Complex.abs_re_le_norm (deriv riemannZeta₁ s / riemannZeta₁ s),
        neg_abs_le (deriv riemannZeta₁ s / riemannZeta₁ s).re, le_abs_self B]
    nlinarith [abs_nonneg C]

/-- **The optimisation step of the zero-free region argument.** Let `a > b > 0` and `A > 0`. There
is `c > 0`, depending only on `a`, `b`, `A`, such that for every `L ≥ 1` and `β ≤ 1`: if
`a / (σ - β) < b / (σ - 1) + A L` for all `1 < σ ≤ 2`, then `β < 1 - c / L`. -/
theorem lt_one_sub_div_of_forall_div_sub_lt {a b A : ℝ} (hb : 0 < b) (hab : b < a)
    (hA : 0 < A) :
    ∃ c > 0, ∀ L β : ℝ, 1 ≤ L → β ≤ 1 →
      (∀ σ : ℝ, 1 < σ → σ ≤ 2 → a / (σ - β) < b / (σ - 1) + A * L) →
      β < 1 - c / L := by
  set δ : ℝ := min 1 ((a - b) / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hAδ : A * δ ≤ (a - b) / 2 := by
    have : δ ≤ (a - b) / (2 * A) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨δ * (a - b) / (a + b), by apply div_pos <;> nlinarith, ?_⟩
  intro L β hL hβ h
  by_contra hcon
  push Not at hcon
  have hLpos : 0 < L := by linarith
  have hσ1 : 1 < 1 + δ / L := by have := div_pos hδpos hLpos; linarith
  have hσ2 : 1 + δ / L ≤ 2 := by
    have : δ / L ≤ 1 := by rw [div_le_one hLpos]; linarith
    linarith
  have key := h (1 + δ / L) hσ1 hσ2
  set c := δ * (a - b) / (a + b) with hc
  have hcpos : 0 < c := by rw [hc]; apply div_pos <;> nlinarith
  have hpos : 0 < 1 + δ / L - β := by have := div_pos hδpos hLpos; linarith
  have hle : 1 + δ / L - β ≤ (δ + c) / L := by
    rw [add_div]; linarith
  have h1 : a / ((δ + c) / L) ≤ a / (1 + δ / L - β) :=
    div_le_div_of_nonneg_left (by linarith) hpos hle
  have h2 : a / ((δ + c) / L) = (a + b) * L / (2 * δ) := by
    have hab0 : a + b ≠ 0 := by linarith
    have : δ + c = δ * (2 * a) / (a + b) := by rw [hc]; field_simp; ring
    rw [this]
    have ha0 : a ≠ 0 := by linarith
    field_simp
  have h3 : b / (1 + δ / L - 1) + A * L = (b + A * δ) * L / δ := by
    have : 1 + δ / L - 1 = δ / L := by ring
    rw [this]; field_simp
  have h4 : (b + A * δ) * L / δ ≤ (a + b) * L / (2 * δ) := by
    rw [div_le_div_iff₀ hδpos (by positivity)]
    nlinarith [mul_nonneg (mul_pos hLpos hδpos).le
      (show (0 : ℝ) ≤ (a - b) / 2 - A * δ by linarith)]
  linarith

/-! ### Real Dirichlet characters -/

namespace DirichletCharacter

/-- `-ζ'/ζ(σ) < 1 / (σ - 1) + B` on `(1, 2]`, in the form used below. -/
private lemma exists_neg_re_logDeriv_riemannZeta_lt :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re < 1 / (σ - 1) + B :=
  exists_neg_re_logDeriv_riemannZeta_lt_one_div_sub_one_add

/-- A zero of `L(s, χ)` with `Re ρ > 0` is counted at least once by `analyticOrderAt`. -/
private lemma one_le_analyticOrderAt_LFunction {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ1 : χ ≠ 1) {ρ : ℂ} (hρ : LFunction χ ρ = 0) :
    ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt (LFunction χ) ρ := by
  rw [Nat.cast_one, Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero]
  push Not
  exact ⟨(differentiable_LFunction hχ1).analyticAt ρ, hρ⟩

/-- The primitive character inducing a nonprincipal `χ`: it is primitive, nonprincipal, has
modulus at most `q`, and on `Re s > 0` it has the same zeros, with the same orders, as `χ`. -/
private lemma exists_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) :
    ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁), χ₁.IsPrimitive ∧ χ₁ ≠ 1 ∧
      (χ ^ 2 = 1 → χ₁ ^ 2 = 1) ∧ (q₁ : ℝ) ≤ q ∧ (0 : ℝ) < q₁ ∧
      (∀ ρ : ℂ, 0 < ρ.re → (LFunction χ ρ = 0 ↔ LFunction χ₁ ρ = 0)) ∧
      (∀ ρ : ℂ, 0 < ρ.re →
        analyticOrderAt (LFunction χ) ρ = analyticOrderAt (LFunction χ₁) ρ) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ₁eq : changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ :=
    χ.changeLevel_primitiveCharacter
  have hχ₁1 : χ.primitiveCharacter ≠ 1 := by
    intro h; apply hχ1; rw [← hχ₁eq, h, changeLevel_one]
  refine ⟨χ.conductor, this, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, hχ₁1,
    fun hχ2 => ?_, ?_, ?_, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · apply changeLevel_injective χ.conductor_dvd_level
    rw [map_pow, hχ₁eq, hχ2, changeLevel_one]
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  · exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  · rw [← LFunction_changeLevel_eq_zero_iff χ.conductor_dvd_level hχ₁1 hρ, hχ₁eq]
  · rw [← analyticOrderAt_LFunction_changeLevel χ.conductor_dvd_level hχ₁1 hρ, hχ₁eq]

/-- A real nonprincipal character has modulus at least `2`. -/
private lemma two_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) :
    2 ≤ q := by
  rcases Nat.lt_or_ge q 2 with h | h
  · exfalso
    have hq1 : q = 1 := by have := NeZero.ne q; omega
    subst hq1
    exact hχ1 (level_one χ)
  · exact h

private lemma one_lt_log_four : 1 < Real.log 4 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

/-- **No zeros off the real axis near `1`.** There is an absolute constant `c > 0` such that for
`0 < δ < c` and every real nonprincipal Dirichlet character `χ` modulo `q`, `L(s, χ)` has no zero
with `σ > 1 - δ / (4 log (q (|t| + 2)))` and `|t| > δ / log q`. -/
theorem LFunction_ne_zero_of_sq_eq_one_of_abs_im_gt :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ < c →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
        ∀ s : ℂ, 1 - δ / (4 * Real.log (q * (|s.im| + 2))) < s.re →
          δ / Real.log q < |s.im| → LFunction χ s ≠ 0 := by
  classical
  have hRgen : ∀ a b : ℝ, 0 < a → 0 < |b| →
      a / (a * a + 2 * b * (2 * b)) ≤ 1 / (4 * |b|) := by
    intro a b ha hb
    have hb2 : 0 < b * b := by nlinarith [sq_abs b]
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [sq_nonneg (a - 2 * |b|), sq_abs b]
  -- the final arithmetic, at `σ = 1 + 2u`, `u = δ / ℓ`
  have hEnd : ∀ u β K δ ℓ g : ℝ, 0 < u → u * ℓ = δ → 36 * K * δ < 1 →
      1 - u / 4 < β → β < 1 → g < 1 / (4 * u) →
      4 / (1 + 2 * u - β) < 3 / (1 + 2 * u - 1) + g + K * ℓ → False := by
    intro u β K δ ℓ g hu huℓ hK hβ hβ1 hg H
    have hx : 0 < 1 + 2 * u - β := by linarith
    have hA : 16 / (9 * u) < 4 / (1 + 2 * u - β) := by
      rw [div_lt_div_iff₀ (by positivity) hx]; linarith
    rw [show 1 + 2 * u - 1 = 2 * u by ring] at H
    have hsplit : 16 / (9 * u) - 3 / (2 * u) - 1 / (4 * u) = 1 / (36 * u) := by
      field_simp; ring
    have h36 : 1 / (36 * u) < K * ℓ := by linarith
    rw [div_lt_iff₀ (by positivity)] at h36
    have e36 : K * ℓ * (36 * u) = 36 * K * δ := by rw [← huℓ]; ring
    linarith
  obtain ⟨C, hHad⟩ := exists_neg_re_logDeriv_LFunction_le
  obtain ⟨B, hX⟩ := exists_neg_re_logDeriv_riemannZeta_lt
  obtain ⟨c₁, hc₁, hζ⟩ := exists_neg_re_logDeriv_riemannZeta_lt_re_one_div_sub_one_add_log
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 * |B| + 4 * |C| + c₁ + 3 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨min (1 / 2) (1 / (36 * K)), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδc q _ χ hχ2 hχ1 ρ hre hγq hzero
  have hδ1 : δ < 1 / 2 := lt_of_lt_of_le hδc (min_le_left _ _)
  have hδK : δ < 1 / (36 * K) := lt_of_lt_of_le hδc (min_le_right _ _)
  have hq2 := two_le_of_ne_one hχ1
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = ρ.im := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ρ.re := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (q * (|γ| + 2)) := ⟨_, rfl⟩
  rw [← hγ, ← hℓ, ← hβ] at hre
  rw [← hγ] at hγq
  have hq2r : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlq : Real.log q ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log (by linarith)
      (le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg γ]))
  have hqγ : 2 * (|γ| + 2) ≤ q * (|γ| + 2) :=
    mul_le_mul_of_nonneg_right hq2r (by positivity)
  have hℓ1 : 1 < ℓ := by
    have h4 : Real.log 4 ≤ ℓ := by
      rw [hℓ]; exact Real.log_le_log (by norm_num) (by linarith only [hqγ, abs_nonneg γ])
    linarith only [h4, one_lt_log_four]
  have hℓpos : 0 < ℓ := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = δ / ℓ := ⟨_, rfl⟩
  have hupos : 0 < u := by rw [hu]; positivity
  have huℓ : u * ℓ = δ := by rw [hu]; exact div_mul_cancel₀ δ hℓpos.ne'
  have hu2 : u < 1 / 2 := by
    rw [hu, div_lt_iff₀ hℓpos]; linarith only [hℓ1, hδ1, hδ]
  have hre' : 1 - u / 4 < β := by
    have : δ / (4 * ℓ) = u / 4 := by rw [hu]; ring
    linarith
  have hβ0 : 0 < β := by linarith
  have hγ0 : 0 < |γ| := lt_trans (by positivity) hγq
  -- the primitive character inducing `χ`, still real
  obtain ⟨q₁, _, χ₁, hχ₁p, hχ₁1, hχ₁2, hq₁, hq₁0, hzeq, -⟩ := exists_primitive hχ1
  have hχ₁2 := hχ₁2 hχ2
  have hzero₁ : LFunction χ₁ ρ = 0 := (hzeq ρ (by rw [← hβ]; exact hβ0)).mp hzero
  have hβ1 : β < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ₁ (Or.inl hχ₁1) (by rw [← hβ]; exact not_lt.mp h)
      hzero₁
  have hkey : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      4 / (σ - β) < 3 / (σ - 1) + 1 / (4 * |γ|) + K * ℓ := by
    intro σ h1 h2
    have e341 := re_neg_logDeriv_three_four_one_nonneg χ₁ γ h1
    rw [hχ₁2] at e341
    have eX := hX σ h1 h2
    have hs1 : 1 < ((σ : ℂ) + γ * Complex.I).re := by simpa using h1
    have hs1' : ((σ : ℂ) + γ * Complex.I).re ≤ 2 := by simpa using h2
    have hs2 : 1 < ((σ : ℂ) + 2 * γ * Complex.I).re := by simpa using h1
    have hσβ : 0 < σ - β := by linarith
    have hρterm : (1 / ((σ : ℂ) + γ * Complex.I - ρ)).re = 1 / (σ - β) := by
      have : (σ : ℂ) + γ * Complex.I - ρ = ((σ - β : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hβ, hγ]
      rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    have eY := hHad _ χ₁ hχ₁p hχ₁1 _ hs1 hs1' {ρ} (fun _ => 1) (by
      simpa using ⟨hβ ▸ hβ0, one_le_analyticOrderAt_LFunction hχ₁1 hzero₁⟩)
    simp only [Finset.sum_singleton, Nat.cast_one, one_mul, hρterm] at eY
    have eZ := neg_re_logDeriv_LFunction_changeLevel_le (N := q₁) (one_dvd _)
      (χ := (1 : DirichletCharacter ℂ 1)) hs2
    rw [changeLevel_one, LFunction_modOne_eq, logDeriv_apply riemannZeta] at eZ
    have eζ := hζ _ hs2
    have him1 : ((σ : ℂ) + γ * Complex.I).im = γ := by simp
    have him2 : ((σ : ℂ) + 2 * γ * Complex.I).im = 2 * γ := by simp
    rw [him1] at eY
    rw [him2] at eζ
    have hR : (1 / ((σ : ℂ) + 2 * γ * Complex.I - 1)).re ≤ 1 / (4 * |γ|) := by
      have : (σ : ℂ) + 2 * γ * Complex.I - 1 = ⟨σ - 1, 2 * γ⟩ := by
        apply Complex.ext <;> simp
      rw [this, one_div, Complex.inv_re, Complex.normSq_mk]
      exact hRgen _ _ (by linarith) hγ0
    have hl1 : Real.log (q₁ * (|γ| + 2)) ≤ ℓ := by
      rw [hℓ]
      exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hq₁ (by positivity))
    have hl2 : Real.log (|2 * γ| + 2) ≤ ℓ := by
      rw [hℓ, abs_mul, abs_two]
      exact Real.log_le_log (by positivity) (by linarith only [hqγ])
    have hl3 : Real.log q₁ ≤ ℓ := le_trans (Real.log_le_log hq₁0 hq₁) hlq
    have hc1l := mul_le_mul_of_nonneg_left hl2 hc₁.le
    have hb1 : 3 * B ≤ 3 * |B| * ℓ := by
      have := mul_le_mul_of_nonneg_left hℓ1.le (abs_nonneg B)
      linarith only [this, le_abs_self B]
    have hb2 : 4 * C ≤ 4 * |C| * ℓ := by
      have := mul_le_mul_of_nonneg_left hℓ1.le (abs_nonneg C)
      linarith only [this, le_abs_self C]
    have hKℓ : K * ℓ = 3 * |B| * ℓ + 4 * |C| * ℓ + c₁ * ℓ + 3 * ℓ := by rw [hK]; ring
    simp only [Complex.neg_re] at e341
    have h3 : 3 / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
    have h4 : 4 / (σ - β) = 4 * (1 / (σ - β)) := by ring
    rw [h3, h4, hKℓ]
    linarith only [e341, eX, eY, eZ, eζ, hR, hl1, hl3, hc1l, hb1, hb2]
  -- take `σ = 1 + 2δ/ℓ`
  have hσ1 : 1 < 1 + 2 * u := by linarith
  have hσ2 : 1 + 2 * u ≤ 2 := by linarith
  have H := hkey _ hσ1 hσ2
  have hB' : 1 / (4 * |γ|) < 1 / (4 * u) := by
    have : u ≤ δ / Real.log q := by
      rw [hu]; exact div_le_div_of_nonneg_left hδ.le hlogq hlq
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  have h36 : 36 * K * δ < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hδK; linarith
  exact hEnd u β K δ ℓ _ hupos huℓ h36 hre' hβ1 hB' H

/-- **At most one zero near `1`, counted with multiplicity.** There is an absolute constant
`c > 0` such that for every real nonprincipal Dirichlet character `χ` modulo `q` (`χ ≠ 1`,
`χ ^ 2 = 1`), the zeros of `L(s, χ)` in the region `σ > 1 - c / log (q (|t| + 2))`, counted with
multiplicity, number at most one: for any finite set `S` of such zeros and multiplicities
`m ρ` bounded by the orders of vanishing, `∑_{ρ ∈ S} m ρ ≤ 1`. -/
theorem sum_le_one_of_sq_eq_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ (S : Finset ℂ) (m : ℂ → ℕ), (∀ ρ ∈ S, LFunction χ ρ = 0 ∧
        1 - c / Real.log (q * (|ρ.im| + 2)) < ρ.re ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (LFunction χ) ρ) →
      ∑ ρ ∈ S, m ρ ≤ 1 := by
  classical
  -- one zero term, at a real point to the right of `1`
  have hTerm : ∀ (L a δ : ℝ) (ρ : ℂ), 0 < L → 0 < a → δ ≤ a / 9 → 0 < 1 - ρ.re →
      (1 - ρ.re) * L < δ / 2 → ρ.im ^ 2 * L ^ 2 ≤ 9 * δ ^ 2 →
      4 / 5 * (L / a) ≤ (1 / (((1 + a / L : ℝ) : ℂ) - ρ)).re := by
    intro L a δ ρ hL ha hδa hβ hβL hγL
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
      neg_mul_neg]
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 + a / L - ρ.re := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ρ.im := ⟨_, rfl⟩
    rw [← hd, ← hg]
    rw [← hg] at hγL
    have hdL : d * L = a + (1 - ρ.re) * L := by
      rw [hd]; field_simp; ring
    have hβL0 : 0 < (1 - ρ.re) * L := mul_pos hβ hL
    have hd0 : 0 < d * L := by rw [hdL]; linarith
    have hd0' : 0 < d := pos_of_mul_pos_left hd0 hL.le
    have h1 : d * L ≤ 19 / 18 * a := by rw [hdL]; linarith
    have h1' : L * d * d ≤ 19 / 18 * a * d := by
      have := mul_le_mul_of_nonneg_right h1 hd0'.le; linarith
    have hδ2 : 9 * δ ^ 2 ≤ a ^ 2 / 9 := by
      have hδ0 : 0 ≤ δ := by nlinarith
      have : δ ^ 2 ≤ (a / 9) ^ 2 := pow_le_pow_left₀ hδ0 hδa 2
      nlinarith
    have h2 : (L * (g * g)) * L ≤ (a * d / 9) * L := by
      have hadL : a * a ≤ a * (d * L) := mul_le_mul_of_nonneg_left (by linarith) ha.le
      have e1 : L * (g * g) * L = g ^ 2 * L ^ 2 := by ring
      have e2 : a * d / 9 * L = a * (d * L) / 9 := by ring
      have e3 : a ^ 2 = a * a := by ring
      rw [e1, e2]
      linarith
    have h2' : L * (g * g) ≤ a * d / 9 := le_of_mul_le_mul_right h2 hL
    have hden : 0 < d * d + g * g := by
      have := mul_pos hd0' hd0'
      have := mul_self_nonneg g
      linarith
    have had : 0 ≤ a * d := mul_nonneg ha.le hd0'.le
    rw [le_div_iff₀ hden,
      show 4 / 5 * (L / a) * (d * d + g * g) = (L * d * d + L * (g * g)) * (4 / 5) / a by ring,
      div_le_iff₀ ha]
    linarith
  obtain ⟨C, hHad⟩ := exists_neg_re_logDeriv_LFunction_le
  obtain ⟨B, hX⟩ := exists_neg_re_logDeriv_riemannZeta_lt
  obtain ⟨c₀, hc₀, hNZ⟩ := LFunction_ne_zero_of_sq_eq_one_of_abs_im_gt
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |B| + |C| + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; linarith [abs_nonneg B, abs_nonneg C]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * K) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; positivity
  have hKa : K * a = 1 / 2 := by rw [ha]; field_simp
  have ha2 : a ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hK1 hapos.le
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (c₀ / 2) (a / 9) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by linarith)
  have hδ0 : δ < c₀ := by rw [hδ]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδa : δ ≤ a / 9 := by rw [hδ]; exact min_le_right _ _
  refine ⟨δ / 4, by positivity, ?_⟩
  intro q _ χ hχ1 hχ2 S m hS
  by_contra hne
  push Not at hne
  have hq2 := two_le_of_ne_one hχ1
  have hq2r : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (3 * q) := ⟨_, rfl⟩
  have hL1 : 1 < L := by
    have : Real.log 4 ≤ L := by rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
    linarith [one_lt_log_four]
  have hLpos : 0 < L := by linarith
  have hqq : (q : ℝ) * 2 ≤ q * q := mul_le_mul_of_nonneg_left hq2r (Nat.cast_nonneg q)
  have hLq : L ≤ 3 * Real.log q := by
    have h3 : (q : ℝ) * 3 ≤ q * (q * q) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    have := Real.log_le_log (by positivity) (show 3 * (q : ℝ) ≤ (q : ℝ) ^ 3 by
      rw [show (q : ℝ) ^ 3 = q * (q * q) by ring]; linarith)
    rw [Real.log_pow] at this
    push_cast at this
    rw [hL]; exact this
  have hL2q : L ≤ 2 * Real.log (2 * q) := by
    have := Real.log_le_log (by positivity) (show 3 * (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 by
      rw [show (2 * (q : ℝ)) ^ 2 = 4 * (q * q) by ring]; linarith)
    rw [Real.log_pow] at this
    push_cast at this
    rw [hL]; exact this
  have h2qL : Real.log (2 * q) ≤ L := by
    rw [hL]; exact Real.log_le_log (by positivity) (by linarith)
  -- every zero in the region is close to `1` and close to the real axis
  have hZ : ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - δ / 4 / Real.log (q * (|ρ.im| + 2)) < ρ.re →
      (1 - ρ.re) * L < δ / 2 ∧ ρ.im ^ 2 * L ^ 2 ≤ 9 * δ ^ 2 ∧ 0 < ρ.re := by
    intro ρ hρ hre
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (q * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hℓ] at hre
    have hℓ2 : Real.log (2 * q) ≤ ℓ := by
      have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ |ρ.im| + 2 by
        linarith [abs_nonneg ρ.im]) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
      rw [hℓ]; exact Real.log_le_log (by positivity) (by linarith)
    have hℓL : L ≤ 2 * ℓ := by linarith
    have hℓpos : 0 < ℓ := by linarith
    have h1 : δ / 4 / ℓ ≤ δ / 4 / (L / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : δ / 4 / (L / 2) * L = δ / 2 := by field_simp; ring
    refine ⟨?_, ?_, ?_⟩
    · have : (1 - ρ.re) * L < δ / 4 / (L / 2) * L :=
        mul_lt_mul_of_pos_right (by linarith) hLpos
      linarith
    · have hreg : 1 - δ / (4 * Real.log (q * (|ρ.im| + 2))) < ρ.re := by
        rw [← hℓ, ← div_div]; exact hre
      have hγ : |ρ.im| ≤ δ / Real.log q := by
        by_contra h
        exact hNZ δ hδpos hδ0 q χ hχ2 hχ1 ρ hreg (not_le.mp h) hρ
      have hγ3 : |ρ.im| * L ≤ 3 * δ := by
        rw [le_div_iff₀ hlogq] at hγ
        calc |ρ.im| * L ≤ |ρ.im| * (3 * Real.log q) :=
              mul_le_mul_of_nonneg_left hLq (abs_nonneg ρ.im)
          _ = 3 * (|ρ.im| * Real.log q) := by ring
          _ ≤ 3 * δ := by linarith
      have : ρ.im ^ 2 * L ^ 2 = (|ρ.im| * L) ^ 2 := by rw [mul_pow, sq_abs]
      rw [this]
      have h0 : 0 ≤ |ρ.im| * L := by positivity
      have := pow_le_pow_left₀ h0 hγ3 2
      rw [mul_pow] at this
      norm_num at this
      linarith
    · have : δ / 4 / (L / 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      linarith
  -- the primitive character inducing `χ`
  obtain ⟨q₁, _, χ₁, hχ₁p, hχ₁1, -, hq₁, hq₁0, hzeq, hordeq⟩ := exists_primitive hχ1
  have hρ : ∀ ρ ∈ S, (1 - ρ.re) * L < δ / 2 ∧ ρ.im ^ 2 * L ^ 2 ≤ 9 * δ ^ 2 ∧ 0 < ρ.re :=
    fun ρ hρ => hZ ρ (hS ρ hρ).1 (hS ρ hρ).2.1
  have hβ1 : ∀ ρ ∈ S, 0 < 1 - ρ.re := by
    intro ρ hρS
    have hz := (hzeq ρ (hρ ρ hρS).2.2).mp (hS ρ hρS).1
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ₁ (Or.inl hχ₁1) (by linarith) hz
  -- evaluate at `σ = 1 + a / L`
  have haL : a / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hLpos]; linarith
  have haL0 : 0 < a / L := by positivity
  have hσ1 : 1 < 1 + a / L := by linarith
  have hσ2 : 1 + a / L ≤ 2 := by linarith
  have hs1 : 1 < ((1 + a / L : ℝ) : ℂ).re := by simpa using hσ1
  have hs2 : ((1 + a / L : ℝ) : ℂ).re ≤ 2 := by simpa using hσ2
  have e0 := re_neg_logDeriv_riemannZeta_add_LFunction_nonneg χ₁ hσ1
  have eX := hX (1 + a / L) hσ1 hσ2
  have eY := hHad _ χ₁ hχ₁p hχ₁1 _ hs1 hs2 S m (fun ρ hρS =>
    ⟨(hρ ρ hρS).2.2, by rw [← hordeq ρ (hρ ρ hρS).2.2]; exact (hS ρ hρS).2.2⟩)
  have tsum : 2 * (4 / 5 * (L / a)) ≤
      ∑ ρ ∈ S, (m ρ : ℝ) * (1 / (((1 + a / L : ℝ) : ℂ) - ρ)).re := by
    have h2 : (2 : ℝ) ≤ ∑ ρ ∈ S, (m ρ : ℝ) := by exact_mod_cast hne
    calc 2 * (4 / 5 * (L / a)) ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (4 / 5 * (L / a)) := by
          gcongr
      _ = ∑ ρ ∈ S, (m ρ : ℝ) * (4 / 5 * (L / a)) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun ρ hρS => mul_le_mul_of_nonneg_left
          (hTerm L a δ ρ hLpos hapos hδa (hβ1 ρ hρS) (hρ ρ hρS).1 (hρ ρ hρS).2.1)
          (Nat.cast_nonneg _)
  have him : ((1 + a / L : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  rw [him, abs_zero, zero_add] at eY
  have hl1 : Real.log (q₁ * 2) ≤ L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) h2qL
    linarith
  have hinv : 1 / (1 + a / L - 1) = L / a := by
    rw [show 1 + a / L - 1 = a / L by ring, one_div_div]
  rw [hinv] at eX
  have hW : K * L = L / a / 2 := by
    rw [show K * L = L / a * (K * a) by
      rw [mul_comm K a, ← mul_assoc, div_mul_cancel₀ _ hapos.ne', mul_comm], hKa]
    ring
  have hb : B ≤ |B| * L := by
    have := mul_le_mul_of_nonneg_left hL1.le (abs_nonneg B)
    linarith [le_abs_self B]
  have hc : C ≤ |C| * L := by
    have := mul_le_mul_of_nonneg_left hL1.le (abs_nonneg C)
    linarith [le_abs_self C]
  have hKL : K * L = |B| * L + |C| * L + L := by rw [hK]; ring
  have hLa : 0 < L / a := by positivity
  simp only [Complex.neg_re] at e0
  linarith only [e0, eX, eY, tsum, hl1, hW, hb, hc, hKL, hLa, hLpos]

/-- **At most one exceptional zero.** There is an absolute constant `c > 0` such that for every
real nonprincipal Dirichlet character `χ` modulo `q`, `L(s, χ)` has at most one zero with
`σ > 1 - c / log (q (|t| + 2))`. -/
theorem LFunction_zeros_subsingleton_of_sq_eq_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      Set.Subsingleton {s : ℂ | LFunction χ s = 0 ∧
        1 - c / Real.log (q * (|s.im| + 2)) < s.re} := by
  classical
  obtain ⟨c, hc, h⟩ := sum_le_one_of_sq_eq_one
  refine ⟨c, hc, fun q _ χ hχ1 hχ2 ρ₁ ⟨hz1, hr1⟩ ρ₂ ⟨hz2, hr2⟩ => ?_⟩
  by_contra hne
  have := h q χ hχ1 hχ2 {ρ₁, ρ₂} (fun _ => 1) (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro ρ (rfl | rfl)
    exacts [⟨hz1, hr1, one_le_analyticOrderAt_LFunction hχ1 hz1⟩,
      ⟨hz2, hr2, one_le_analyticOrderAt_LFunction hχ1 hz2⟩])
  rw [Finset.sum_pair hne] at this
  omega

/-- **The exceptional zero is real.** There is an absolute constant `c > 0` such that for every
real nonprincipal Dirichlet character `χ` modulo `q`, every zero `s` of `L(s, χ)` with
`σ > 1 - c / log (q (|t| + 2))` is real. -/
theorem im_eq_zero_of_LFunction_eq_zero_of_sq_eq_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ s : ℂ, LFunction χ s = 0 → 1 - c / Real.log (q * (|s.im| + 2)) < s.re → s.im = 0 := by
  obtain ⟨c, hc, hsub⟩ := LFunction_zeros_subsingleton_of_sq_eq_one
  refine ⟨c, hc, fun q _ χ hχ1 hχ2 s hs hreg => ?_⟩
  have hχi : χ⁻¹ = χ := by rw [inv_eq_iff_mul_eq_one, ← sq, hχ2]
  have hs' : LFunction χ ((starRingEnd ℂ) s) = 0 := by
    have h := conj_LFunction_conj hχ1 ((starRingEnd ℂ) s)
    simp only [Complex.conj_conj, hχi, hs, map_zero] at h
    exact h.symm
  have h := hsub q χ hχ1 hχ2 (show s ∈ {s : ℂ | LFunction χ s = 0 ∧
      1 - c / Real.log (q * (|s.im| + 2)) < s.re} from ⟨hs, hreg⟩)
    (show (starRingEnd ℂ) s ∈ {s : ℂ | LFunction χ s = 0 ∧
      1 - c / Real.log (q * (|s.im| + 2)) < s.re} from
      ⟨hs', by simpa [Complex.conj_im, Complex.conj_re, abs_neg] using hreg⟩)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- **The exceptional zero is simple.** There is an absolute constant `c > 0` such that for every
real nonprincipal Dirichlet character `χ` modulo `q`, every zero `s` of `L(s, χ)` with
`σ > 1 - c / log (q (|t| + 2))` has order of vanishing `1`. -/
theorem analyticOrderAt_LFunction_eq_one_of_sq_eq_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ s : ℂ, LFunction χ s = 0 → 1 - c / Real.log (q * (|s.im| + 2)) < s.re →
        analyticOrderAt (LFunction χ) s = 1 := by
  obtain ⟨c, hc, h⟩ := sum_le_one_of_sq_eq_one
  refine ⟨c, hc, fun q _ χ hχ1 hχ2 s hs hreg => ?_⟩
  have h1 := one_le_analyticOrderAt_LFunction hχ1 hs
  by_contra hne
  have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (LFunction χ) s := by
    generalize analyticOrderAt (LFunction χ) s = k at h1 hne ⊢
    induction k using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      have hk1 : 1 ≤ k := by exact_mod_cast h1
      have hk : k ≠ 1 := by exact_mod_cast hne
      exact_mod_cast (by omega : 2 ≤ k)
  have := h q χ hχ1 hχ2 {s} (fun _ => 2) (by simpa using ⟨hs, hreg, h2⟩)
  simp at this

end DirichletCharacter
