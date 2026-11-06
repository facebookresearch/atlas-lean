/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeries

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-!
# Series and analyticity facts for Gamma and digamma

For `x > 0`, the digamma series `∑ (1/(j+1) - 1/(x+j+1))` sums to `ψ(x+1) + γ`, where
`ψ = (log ∘ Gamma)'`, and its termwise derivative gives the trigamma series `∑ 1/(y+j+1)²`.
The file also proves that `Complex.Gamma` and `Complex.digamma` are analytic away from the
nonpositive integers, that the complex derivative of `Gamma` restricts to the real one on
`(0, ∞)`, and that `∑ 1/(z+k+1)²` converges absolutely for every complex `z` away from the
negative integers, and that for `1 < s.re` the complex digamma function satisfies
the expansion `ψ(s) + γ = ∑ j, (1/(j+1) - 1/(j+s))` (as a `HasSum` statement).
-/

@[expose] public section

open scoped Real
open Filter Finset Topology

noncomputable section

namespace Real

/-- Auxiliary: `|log (1 + u) - u| ≤ 2 u ^ 2` for `|u| ≤ 1 / 2`. -/
private lemma aux_log_one_add_bound {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have hneg : (-1 / 2 : ℝ) ≤ u := by
    have := neg_le_of_abs_le hu
    linarith
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have hup : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hlow : u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
    have hinv : (0 : ℝ) < 1 / (1 + u) := by positivity
    have h2 := Real.log_le_sub_one_of_pos hinv
    have h2' : Real.log (1 / (1 + u)) = -Real.log (1 + u) := by
      rw [one_div, Real.log_inv]
    rw [h2'] at h2
    have h3 : (1 : ℝ) / (1 + u) - 1 = -u / (1 + u) := by
      field_simp
      ring
    rw [h3] at h2
    have h4 : u / (1 + u) ≤ Real.log (1 + u) := by
      rw [neg_div] at h2
      linarith
    have h5 : u - u / (1 + u) ≤ 2 * u ^ 2 := by
      have h6 : u - u / (1 + u) = u ^ 2 / (1 + u) := by
        field_simp
        ring
      rw [h6]
      have h7 : u ^ 2 / (1 + u) ≤ u ^ 2 / (1 / 2) := by
        apply div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) _
        linarith
      have h8 : u ^ 2 / (1 / 2 : ℝ) = 2 * u ^ 2 := by ring
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Auxiliary: difference quotient of `log` is close to `1 / a`. -/
private lemma aux_log_diff_bound {a h : ℝ} (ha : 0 < a) (hh : |h| ≤ a / 2) (h0 : h ≠ 0) :
    |(Real.log (a + h) - Real.log a) / h - 1 / a| ≤ 2 * |h| / a ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hau : |h / a| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    calc |h| ≤ a / 2 := hh
      _ = 1 / 2 * a := by ring
  have h1u : (0 : ℝ) < 1 + h / a := by
    have hneg : (-1 / 2 : ℝ) ≤ h / a := by
      have := neg_le_of_abs_le hau
      linarith
    linarith
  have hah : a + h = a * (1 + h / a) := by
    field_simp
  have hlog : Real.log (a + h) - Real.log a = Real.log (1 + h / a) := by
    rw [hah, Real.log_mul ha0 (ne_of_gt h1u), add_sub_cancel_left]
  have hu_eq : (h / a) / h = 1 / a := by
    field_simp
  have hdecomp : (Real.log (a + h) - Real.log a) / h - 1 / a
      = (Real.log (1 + h / a) - h / a) / h := by
    rw [hlog, ← hu_eq]
    field_simp
  have hbound := aux_log_one_add_bound hau
  have hu2 : (h / a) ^ 2 = h ^ 2 / a ^ 2 := div_pow h a 2
  have hpos : (0 : ℝ) < |h| := abs_pos.mpr h0
  rw [hdecomp, abs_div]
  have hstep : |Real.log (1 + h / a) - h / a| / |h| ≤ (2 * ((h / a) ^ 2)) / |h| := by
    gcongr
  have hfinal : (2 * ((h / a) ^ 2)) / |h| = 2 * |h| / a ^ 2 := by
    rw [hu2]
    field_simp
    rw [sq_abs]
  linarith [hstep, hfinal, hbound]

/-- Exact form of the difference quotient of `logGammaSeq`. -/
private lemma aux_E_eq (x h : ℝ) (h0 : h ≠ 0) (N : ℕ) :
    (Real.BohrMollerup.logGammaSeq (x + h) N - Real.BohrMollerup.logGammaSeq x N) / h
      = Real.log N
        - ∑ m ∈ Finset.range (N + 1),
          (Real.log (x + h + m) - Real.log (x + m)) / h := by
  have hS : (∑ m ∈ Finset.range (N + 1),
        (Real.log (x + h + (m : ℝ)) - Real.log (x + (m : ℝ))))
      = (∑ m ∈ Finset.range (N + 1), Real.log (x + h + (m : ℝ)))
        - ∑ m ∈ Finset.range (N + 1), Real.log (x + (m : ℝ)) :=
    Finset.sum_sub_distrib _ _
  simp only [Real.BohrMollerup.logGammaSeq]
  conv_rhs => rw [← Finset.sum_div, hS]
  field_simp
  ring

/-- M-test bound for the trigamma majorant on `(0, ∞)`. -/
private lemma aux_sq_sum_bound (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), 1 / (x + m) ^ 2 ≤ 1 / x ^ 2 + Real.pi ^ 2 / 6 := by
  have htail2 : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    have hsplit := Finset.sum_range_succ' (fun j : ℕ => 1 / (j : ℝ) ^ 2) N
    have hz : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
    have hle := Summable.sum_le_tsum (Finset.range (N + 1))
      (fun i _ => by positivity) hasSum_zeta_two.summable
    have hzeta := hasSum_zeta_two.tsum_eq
    have hcongr : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2
        = ∑ k ∈ Finset.range N, 1 / (((k + 1 : ℕ) : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [hcongr]
    linarith
  have hhead : (1 : ℝ) / (x + ((0 : ℕ) : ℝ)) ^ 2 = 1 / x ^ 2 := by simp
  have hterm : ∀ k ∈ Finset.range N,
      1 / (x + (((k + 1 : ℕ) : ℝ))) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle2 : (k : ℝ) + 1 ≤ x + (((k + 1 : ℕ) : ℝ)) := by
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [this]
      linarith
    have hsq : ((k : ℝ) + 1) ^ 2 ≤ (x + (((k + 1 : ℕ) : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hk1.le hle2 2
    exact one_div_le_one_div_of_le (by positivity) hsq
  have hsplit2 := Finset.sum_range_succ' (fun m : ℕ => 1 / (x + (m : ℝ)) ^ 2) N
  rw [hsplit2, hhead]
  have := Finset.sum_le_sum hterm
  linarith

/-- Uniform (in `N`) closeness of the difference quotient to `D_N`. -/
private lemma aux_E_D_bound (x h : ℝ) (hx : 0 < x) (hh : |h| ≤ x / 2) (h0 : h ≠ 0) (N : ℕ) :
    dist (Real.log N - ∑ m ∈ Finset.range (N + 1),
            (Real.log (x + h + m) - Real.log (x + m)) / h)
      (Real.log N - ∑ m ∈ Finset.range (N + 1), 1 / (x + m))
      ≤ 2 * |h| * (1 / x ^ 2 + Real.pi ^ 2 / 6) := by
  have hdiff : (Real.log N - ∑ m ∈ Finset.range (N + 1),
        (Real.log (x + h + m) - Real.log (x + m)) / h)
        - (Real.log N - ∑ m ∈ Finset.range (N + 1), 1 / (x + m))
      = ∑ m ∈ Finset.range (N + 1),
        (1 / (x + m) - (Real.log (x + h + m) - Real.log (x + m)) / h) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [Real.dist_eq, hdiff]
  have hterm : ∀ m ∈ Finset.range (N + 1),
      |1 / (x + (m : ℝ)) - (Real.log (x + h + m) - Real.log (x + m)) / h|
        ≤ 2 * |h| / (x + (m : ℝ)) ^ 2 := by
    intro m _
    have ham : (0 : ℝ) < x + m := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hhm : |h| ≤ (x + (m : ℝ)) / 2 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have e1 : x + h + (m : ℝ) = (x + (m : ℝ)) + h := by ring
    rw [e1]
    have hmain := aux_log_diff_bound ham hhm h0
    rw [abs_sub_comm]
    exact hmain
  calc |∑ m ∈ Finset.range (N + 1),
          (1 / (x + (m : ℝ)) - (Real.log (x + h + m) - Real.log (x + m)) / h)|
      ≤ ∑ m ∈ Finset.range (N + 1),
          |1 / (x + (m : ℝ)) - (Real.log (x + h + m) - Real.log (x + m)) / h| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range (N + 1), 2 * |h| / (x + (m : ℝ)) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * |h| * (∑ m ∈ Finset.range (N + 1), 1 / (x + (m : ℝ)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
    _ ≤ 2 * |h| * (1 / x ^ 2 + Real.pi ^ 2 / 6) := by
        apply mul_le_mul_of_nonneg_left (aux_sq_sum_bound x hx N) (by positivity)

/-- Three-term triangle inequality for `dist`. -/
private lemma aux_dist_tri {a b c d : ℝ} : dist a d ≤ dist a b + dist b c + dist c d := by
  have t1 := dist_triangle a b d
  have t2 := dist_triangle b c d
  linarith

/-- The difference quotients `D_N(x)` tend to `deriv (log ∘ Gamma) x`. -/
private lemma aux_D_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun N : ℕ => Real.log N - ∑ m ∈ Finset.range (N + 1), 1 / (x + m))
      atTop (𝓝 (deriv (fun t => Real.log (Real.Gamma t)) x)) := by
  set f : ℝ → ℝ := fun t => Real.log (Real.Gamma t) with hf_def
  have hxU : ∀ m : ℕ, x ≠ -((m : ℕ) : ℝ) := by
    intro m hcon
    have hle : x ≤ 0 := by
      rw [hcon]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    linarith
  have hdiff : DifferentiableAt ℝ f x :=
    (Real.differentiableAt_Gamma hxU).log (Real.Gamma_ne_zero hxU)
  have hslope_lim := hdiff.hasDerivAt.tendsto_slope
  have hslope_eq : ∀ h : ℝ, h ≠ 0 →
      slope f x (x + h) = (f (x + h) - f x) / h := by
    intro h _
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    rw [div_eq_mul_inv]
    ring
  set C₀ : ℝ := 1 / x ^ 2 + Real.pi ^ 2 / 6 with hC₀def
  have hC₀pos : 0 < C₀ := by
    have h1 : (0 : ℝ) < 1 / x ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have hev_slope : ∀ᶠ y in 𝓝[≠] x, dist (slope f x y) (deriv f x) < ε / 3 :=
    (Metric.tendsto_nhds.mp hslope_lim) (ε / 3) hε3
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hev_slope)
  set δ := min (min δ₁ (x / 2)) (ε / (6 * C₀)) with hδdef
  have hδpos : 0 < δ := by
    have hEp : (0 : ℝ) < ε / (6 * C₀) := by positivity
    rw [hδdef]
    simp only [lt_min_iff]
    exact ⟨⟨hδ₁pos, by linarith⟩, hEp⟩
  have hδ1 : δ ≤ δ₁ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ x / 2 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ ≤ ε / (6 * C₀) := by
    rw [hδdef]
    exact min_le_right _ _
  -- fix h* = δ / 2
  set hstar := δ / 2 with hhstar_def
  have hhstar_pos : 0 < hstar := by linarith
  have hhstar_ne : hstar ≠ 0 := ne_of_gt hhstar_pos
  have hhstar_lt_δ₁ : dist (x + hstar) x < δ₁ := by
    rw [Real.dist_eq]
    have heq : (x + hstar) - x = hstar := by ring
    rw [heq, abs_of_pos hhstar_pos, hhstar_def]
    linarith
  have hhstar_abs : |hstar| ≤ x / 2 := by
    rw [abs_of_pos hhstar_pos, hhstar_def]
    linarith
  have hxstar : 0 < x + hstar := by linarith
  have hquot_close : dist ((f (x + hstar) - f x) / hstar) (deriv f x) < ε / 3 := by
    have hne : x + hstar ∈ ({x} : Set ℝ)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      apply hhstar_ne
      linarith
    have hmem := hδ₁ (x + hstar) hhstar_lt_δ₁ hne
    rw [← hslope_eq hstar hhstar_ne]
    exact hmem
  -- E_N(h*) → quotient
  have hE_lim : Tendsto
      (fun N : ℕ => (Real.BohrMollerup.logGammaSeq (x + hstar) N
        - Real.BohrMollerup.logGammaSeq x N) / hstar)
      atTop (𝓝 ((f (x + hstar) - f x) / hstar)) := by
    have h1 := Real.BohrMollerup.tendsto_log_gamma hxstar
    have h2 := Real.BohrMollerup.tendsto_log_gamma hx
    have hsub := h1.sub h2
    have := hsub.div_const hstar
    simpa [hf_def] using this
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hE_lim) (ε / 3) hε3
  refine ⟨N₀, fun N hN => ?_⟩
  have hE_close := hN₀ N hN
  rw [aux_E_eq x hstar hhstar_ne N] at hE_close
  have hED := aux_E_D_bound x hstar hx hhstar_abs hhstar_ne N
  rw [← hC₀def, dist_comm] at hED
  have hstar_small : 2 * |hstar| * C₀ < ε / 3 := by
    have hC₀ne : C₀ ≠ 0 := ne_of_gt hC₀pos
    have h1 : hstar ≤ ε / (6 * C₀) / 2 := by
      rw [hhstar_def]
      linarith
    have h2 : (0 : ℝ) ≤ 2 * C₀ := mul_nonneg (by norm_num) hC₀pos.le
    have hmono : 2 * hstar * C₀ ≤ 2 * (ε / (6 * C₀) / 2) * C₀ := by
      calc 2 * hstar * C₀ = (2 * C₀) * hstar := by ring
        _ ≤ (2 * C₀) * (ε / (6 * C₀) / 2) := mul_le_mul_of_nonneg_left h1 h2
        _ = 2 * (ε / (6 * C₀) / 2) * C₀ := by ring
    have heq : 2 * (ε / (6 * C₀) / 2) * C₀ = ε / 6 := by
      field_simp
    rw [abs_of_pos hhstar_pos]
    linarith
  -- conclude by the three-term triangle inequality
  have hfin : dist (Real.log ↑N - ∑ m ∈ Finset.range (N + 1), 1 / (x + ↑m)) (deriv f x)
      < ε := by
    calc dist (Real.log ↑N - ∑ m ∈ Finset.range (N + 1), 1 / (x + ↑m)) (deriv f x)
        ≤ dist (Real.log ↑N - ∑ m ∈ Finset.range (N + 1), 1 / (x + ↑m))
              (Real.log ↑N - ∑ m ∈ Finset.range (N + 1),
                (Real.log (x + hstar + ↑m) - Real.log (x + ↑m)) / hstar)
            + dist (Real.log ↑N - ∑ m ∈ Finset.range (N + 1),
                (Real.log (x + hstar + ↑m) - Real.log (x + ↑m)) / hstar)
              ((f (x + hstar) - f x) / hstar)
            + dist ((f (x + hstar) - f x) / hstar) (deriv f x) := aux_dist_tri
      _ < (2 * |hstar| * C₀ + ε / 3) + ε / 3 :=
          add_lt_add (add_lt_add_of_le_of_lt hED hE_close) hquot_close
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith [hstar_small]
      _ = ε := by ring
  exact hfin

/-- **Summability of the Basel series.** The series of real numbers
$\sum_{j \ge 0} \frac{1}{(j+1)^2}$ is summable. -/
theorem summable_one_div_add_nat_succ_sq : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).mpr
    hasSum_zeta_two.summable
  have hcongr : (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ) ^ 2)
      = (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    funext n
    push_cast
    ring
  rwa [hcongr] at h

/-- `harmonic` as an explicit sum. -/
private lemma aux_harmonic_eq_sum (N : ℕ) :
    harmonic N = ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℚ))⁻¹ := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ n ih =>
    rw [harmonic_succ, ih, Finset.sum_range_succ]

/-- Algebraic rewrite of `D_N` via harmonic numbers. -/
private lemma aux_D_rewrite (x : ℝ) (N : ℕ) :
    Real.log (N : ℝ) - ∑ m ∈ Finset.range (N + 1), 1 / (x + (m : ℝ))
      = -(((harmonic N : ℚ) : ℝ) - Real.log (N : ℝ))
        + (∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) - 1 / (x + (k : ℝ) + 1)))
        - 1 / x := by
  have hH : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
    rw [aux_harmonic_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [one_div]
  have hS := Finset.sum_range_succ' (fun m : ℕ => 1 / (x + (m : ℝ))) N
  rw [hS]
  simp only [Finset.sum_sub_distrib]
  rw [hH]
  push_cast
  ring_nf

/-- Summability of the digamma-series terms. -/
private lemma aux_digamma_terms_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)) := by
  have hbound : ∀ j : ℕ,
      ‖1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)‖ ≤ x / ((j : ℝ) + 1) ^ 2 := by
    intro j
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hxj : (0 : ℝ) < x + (j : ℝ) + 1 := by linarith
    have heq : 1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)
        = x / (((j : ℝ) + 1) * (x + (j : ℝ) + 1)) := by
      field_simp
      ring
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ ((j : ℝ) + 1) * (x + (j : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hj1.le
      linarith
    have hsmall : (0 : ℝ) < ((j : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
    have hstep : x / (((j : ℝ) + 1) * (x + (j : ℝ) + 1))
        ≤ x / (((j : ℝ) + 1) * ((j : ℝ) + 1)) :=
      div_le_div_of_nonneg_left hx.le hsmall hle
    have hsq : ((j : ℝ) + 1) * ((j : ℝ) + 1) = ((j : ℝ) + 1) ^ 2 := by ring
    rwa [hsq] at hstep
  have hmajor : Summable (fun j : ℕ => x / ((j : ℝ) + 1) ^ 2) := by
    have h := summable_one_div_add_nat_succ_sq.mul_left x
    simpa [div_eq_mul_inv] using h
  exact hmajor.of_norm_bounded hbound

/-- **Digamma series on the positive reals.** For every real $x > 0$, the series
$\sum_{j=0}^{\infty} \left(\frac{1}{j+1} - \frac{1}{x+j+1}\right)$ has sum $\psi(x+1) + \gamma$,
where $\psi = (\log \Gamma)'$ with $\Gamma$ the real Gamma function, and $\gamma$ is the
Euler–Mascheroni constant. -/
theorem hasSum_digamma_series (x : ℝ) (hx : 0 < x) :
    HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1))
      (deriv (fun t => Real.log (Real.Gamma t)) (x + 1)
        + Real.eulerMascheroniConstant) := by
  set f : ℝ → ℝ := fun t => Real.log (Real.Gamma t) with hf_def
  have hxU : ∀ m : ℕ, x ≠ -((m : ℕ) : ℝ) := by
    intro m hcon
    have hle : x ≤ 0 := by
      rw [hcon]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    linarith
  have hx1U : ∀ m : ℕ, x + 1 ≠ -((m : ℕ) : ℝ) := by
    intro m hcon
    have hle : x + 1 ≤ 0 := by
      rw [hcon]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    linarith
  have hdiff : DifferentiableAt ℝ f x := (Real.differentiableAt_Gamma hxU).log
    (Real.Gamma_ne_zero hxU)
  have hdiff1 : DifferentiableAt ℝ f (x + 1) := (Real.differentiableAt_Gamma hx1U).log
    (Real.Gamma_ne_zero hx1U)
  have hsum := aux_digamma_terms_summable x hx
  -- limit of rewritten D_N
  have hD := aux_D_tendsto x hx
  have hDeq : ∀ N : ℕ, (Real.log (N : ℝ) - ∑ m ∈ Finset.range (N + 1), 1 / (x + (m : ℝ)))
      = (-(((harmonic N : ℚ) : ℝ) - Real.log (N : ℝ)))
        + (∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) - 1 / (x + (k : ℝ) + 1))) - 1 / x :=
    aux_D_rewrite x
  have hD' := hD.congr (fun N => hDeq N)
  have hlim1 := Real.tendsto_harmonic_sub_log
  have hlim2 := hsum.hasSum.tendsto_sum_nat
  have hcomb : Tendsto
      (fun N : ℕ => (-(((harmonic N : ℚ) : ℝ) - Real.log (N : ℝ)))
        + (∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) - 1 / (x + (k : ℝ) + 1))) - 1 / x)
      atTop (𝓝 ((-Real.eulerMascheroniConstant
        + (∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)))) - 1 / x)) :=
    ((hlim1.neg.add hlim2).sub_const (1 / x))
  have hval : deriv f x
      = (-Real.eulerMascheroniConstant
        + (∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)))) - 1 / x :=
    tendsto_nhds_unique hD' hcomb
  -- recurrence for deriv f
  have hrec : deriv f (x + 1) = deriv f x + x⁻¹ := by
    have heq_on : (fun t => f (t + 1)) =ᶠ[𝓝 x] (fun t => f t + Real.log t) := by
      apply Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx)
      intro t ht
      simp only [Set.mem_Ioi] at ht
      have hG := Real.Gamma_add_one (ne_of_gt ht)
      change Real.log (Real.Gamma (t + 1)) = Real.log (Real.Gamma t) + Real.log t
      rw [hG, Real.log_mul (ne_of_gt ht) (ne_of_gt (Real.Gamma_pos_of_pos ht))]
      ring
    have hL : HasDerivAt (fun t => f (t + 1)) (deriv f (x + 1)) x := by
      have h := hdiff1.hasDerivAt.comp x ((hasDerivAt_id' x).add_const 1)
      simpa [Function.comp_def] using h
    have hR : HasDerivAt (fun t => f t + Real.log t) (deriv f x + x⁻¹) x :=
      hdiff.hasDerivAt.add (Real.hasDerivAt_log (ne_of_gt hx))
    have hcongr := hL.congr_of_eventuallyEq heq_on.symm
    have := hcongr.unique hR
    simpa using this
  have hfinal : deriv f (x + 1) + Real.eulerMascheroniConstant
      = ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1)) := by
    rw [hrec, inv_eq_one_div]
    linarith [hval]
  rw [hfinal]
  exact hsum.hasSum

/-- **Derivative of the digamma series.** For every real $y > 0$, the real function
$z \mapsto \sum_{j=0}^{\infty} \left(\frac{1}{j+1} - \frac{1}{z+j+1}\right)$ is differentiable
at $y$ with derivative $\sum_{j=0}^{\infty} \frac{1}{(y+j+1)^2}$. -/
theorem hasDerivAt_tsum_digamma_series (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z => ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (z + (j : ℝ) + 1)))
      (∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2) y := by
  have hu : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := summable_one_div_add_nat_succ_sq
  have hg : ∀ j : ℕ, ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => 1 / ((j : ℝ) + 1) - 1 / (t + (j : ℝ) + 1))
        (1 / (x + (j : ℝ) + 1) ^ 2) x := by
    intro j x hx
    simp only [Set.mem_Ioi] at hx
    have hne : x + (j : ℝ) + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have h1 : HasDerivAt (fun t : ℝ => t + (j : ℝ) + 1) 1 x :=
      ((hasDerivAt_id' x).add_const (j : ℝ)).add_const 1
    have h2 := h1.inv hne
    have h3 := (hasDerivAt_const x (1 / ((j : ℝ) + 1))).sub h2
    rw [inv_eq_one_div] at h3
    have hval3 : (0 : ℝ) - -1 / (x + (j : ℝ) + 1) ^ 2
        = 1 / (x + (j : ℝ) + 1) ^ 2 := by ring
    rw [hval3] at h3
    exact h3
  have hg' : ∀ j : ℕ, ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖1 / (x + (j : ℝ) + 1) ^ 2‖ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j x hx
    simp only [Set.mem_Ioi] at hx
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hle : (j : ℝ) + 1 ≤ x + (j : ℝ) + 1 := by linarith
    have hsq : ((j : ℝ) + 1) ^ 2 ≤ (x + (j : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ hj1.le hle 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) hsq
  have hg0 : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / (1 + (j : ℝ) + 1)) :=
    aux_digamma_terms_summable 1 one_pos
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hg hg'
    (Set.mem_Ioi.mpr one_pos) hg0 (Set.mem_Ioi.mpr hy)

/-- **Trigamma series.** For every real $y > 0$, the second derivative of $\log \Gamma$ at
$y + 1$ equals $\sum_{j=0}^{\infty} \frac{1}{(y + j + 1)^2}$, where $\Gamma$ is the real Gamma
function. -/
theorem deriv_deriv_log_Gamma_add_one (y : ℝ) (hy : 0 < y) :
    deriv (deriv (fun t => Real.log (Real.Gamma t))) (y + 1)
      = ∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2 := by
  set f : ℝ → ℝ := fun t => Real.log (Real.Gamma t) with hf_def
  set S : ℝ → ℝ := fun z => ∑' j : ℕ,
    (1 / ((j : ℝ) + 1) - 1 / (z + (j : ℝ) + 1)) with hSdef
  set D : ℝ := ∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2 with hDdef
  have hS : HasDerivAt S D y := hasDerivAt_tsum_digamma_series y hy
  -- identify the tsum with the digamma expression
  have hSeq : S =ᶠ[𝓝 y] (fun z => deriv f (z + 1) + Real.eulerMascheroniConstant) := by
    apply Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy)
    intro z hz
    simp only [Set.mem_Ioi] at hz
    have hser := (hasSum_digamma_series z hz).tsum_eq
    simp only [hSdef]
    exact hser
  have hH : HasDerivAt (fun z => deriv f (z + 1) + Real.eulerMascheroniConstant) D y :=
    hS.congr_of_eventuallyEq hSeq.symm
  -- differentiability of deriv f at y + 1, via S ∘ (· - 1)
  have hdiffD : DifferentiableAt ℝ (deriv f) (y + 1) := by
    have hSmem : Set.Ioi (1 : ℝ) ∈ 𝓝 (y + 1) := Ioi_mem_nhds (by linarith)
    have heq2 : (deriv f) =ᶠ[𝓝 (y + 1)]
        (fun x => (S ∘ fun x_ => x_ - 1) x - Real.eulerMascheroniConstant) := by
      apply Filter.eventuallyEq_of_mem hSmem
      intro t ht
      simp only [Set.mem_Ioi] at ht
      have hser := (hasSum_digamma_series (t - 1) (by linarith)).tsum_eq
      have hcast : t - 1 + 1 = t := by ring
      rw [hcast] at hser
      have hSval : S (t - 1) = deriv f t + Real.eulerMascheroniConstant := by
        simp only [hSdef]
        exact hser
      have happ : (S ∘ fun x_ => x_ - 1) t = S (t - 1) := rfl
      linarith
    have houter : HasDerivAt S (deriv S y) (y + 1 - 1) := by
      have heq : y + 1 - 1 = y := by ring
      rw [heq]
      exact hS.differentiableAt.hasDerivAt
    have hcomp0 := HasDerivAt.comp (y + 1) houter
      ((hasDerivAt_id' (y + 1)).sub_const 1)
    have hsub0 := hcomp0.sub_const Real.eulerMascheroniConstant
    exact (hsub0.congr_of_eventuallyEq heq2).differentiableAt
  have hH2 : HasDerivAt (fun z => deriv f (z + 1) + Real.eulerMascheroniConstant)
      (deriv (deriv f) (y + 1)) y := by
    have hcomp0 := HasDerivAt.comp y hdiffD.hasDerivAt ((hasDerivAt_id' y).add_const 1)
    have hadd0 := hcomp0.add_const Real.eulerMascheroniConstant
    rw [mul_one] at hadd0
    refine hadd0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => rfl)
  have huniq := hH2.unique hH
  exact huniq

/-- **Logarithmic derivative of the real Gamma function.** For every real $u > 0$, the
derivative of $\log \Gamma$ at $u$ equals $\Gamma'(u) / \Gamma(u)$, where $\Gamma$ is the real
Gamma function. -/
theorem deriv_log_Gamma (u : ℝ) (hu : 0 < u) :
    deriv (fun t => Real.log (Real.Gamma t)) u
      = deriv Real.Gamma u / Real.Gamma u := by
  have hU : ∀ m : ℕ, u ≠ -((m : ℕ) : ℝ) := by
    intro m hcon
    have hle : u ≤ 0 := by
      rw [hcon]
      exact neg_nonpos.mpr (Nat.cast_nonneg m)
    linarith
  exact ((Real.differentiableAt_Gamma hU).hasDerivAt.log
    (Real.Gamma_ne_zero hU)).deriv

end Real

namespace Complex

/-- **Analyticity of the Gamma function.** The complex Gamma function is analytic at every
$w \in \mathbb{C}$ that is not a nonpositive integer. -/
theorem analyticAt_Gamma (w : ℂ) (hw : ∀ m : ℕ, w ≠ -((m : ℕ) : ℂ)) :
    AnalyticAt ℂ Complex.Gamma w := by
  set M : ℝ := ‖w‖ with hMdef
  set B : ℕ := ⌈M + 2⌉₊ with hBdef
  have hMB : M + 2 ≤ (B : ℝ) := Nat.le_ceil (M + 2)
  have hBpos : 0 < B := by
    have hpos : (0 : ℝ) < M + 2 := by
      have hnn : (0 : ℝ) ≤ M := norm_nonneg _
      linarith
    exact Nat.ceil_pos.mpr hpos
  set f : ℕ → ℝ := fun m => ‖w - (-((m : ℕ) : ℂ))‖ with hfdef
  have hfpos : ∀ m : ℕ, m ∈ Finset.range B → 0 < f m := by
    intro m _
    have hshow : f m = ‖w - (-((m : ℕ) : ℂ))‖ := rfl
    rw [hshow, norm_pos_iff]
    exact sub_ne_zero.mpr (hw m)
  have hIrng : ((Finset.range B).image f).Nonempty :=
    ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hBpos, rfl⟩⟩
  set d : ℝ := ((Finset.range B).image f).min' hIrng with hddef
  have hdpos : 0 < d := by
    obtain ⟨m, hm, hfm⟩ := Finset.mem_image.mp (Finset.min'_mem _ hIrng)
    rw [hddef, ← hfm]
    exact hfpos m hm
  have hdle : ∀ m : ℕ, m ∈ Finset.range B → d ≤ f m := by
    intro m hm
    rw [hddef]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  set r : ℝ := min d 1 / 2 with hrdef
  have hr : 0 < r := by
    rw [hrdef]
    exact div_pos (lt_min hdpos one_pos) two_pos
  have hr1 : r ≤ 1 / 2 := by
    rw [hrdef]
    have h : min d 1 ≤ 1 := min_le_right d 1
    linarith
  have hball : ∀ s : ℂ, s ∈ Metric.ball w r → ∀ m : ℕ, s ≠ -((m : ℕ) : ℂ) := by
    intro s hs m hcon
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have htri2 : f m ≤ ‖w - s‖ + ‖s - (-((m : ℕ) : ℂ))‖ := by
      have heq : w - (-((m : ℕ) : ℂ)) = (w - s) + (s - (-((m : ℕ) : ℂ))) := by
        abel
      have hshow : f m = ‖w - (-((m : ℕ) : ℂ))‖ := rfl
      rw [hshow, heq]
      exact norm_add_le _ _
    have h2 : ‖s - (-((m : ℕ) : ℂ))‖ = 0 := by
      rw [hcon, sub_self, norm_zero]
    have hsym : ‖w - s‖ = ‖s - w‖ := norm_sub_rev _ _
    have hdm_lt : f m < r := by linarith [htri2, h2, hsym, hs]
    by_cases hcase : m < B
    · have hmem : m ∈ Finset.range B := Finset.mem_range.mpr hcase
      have hle := hdle m hmem
      have hr2 : r ≤ d / 2 := by
        rw [hrdef]
        have h : min d 1 ≤ d := min_le_left d 1
        linarith
      linarith
    · have hmB : B ≤ m := not_lt.mp hcase
      have hmB' : (B : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hmB
      have hdm_eq : f m = ‖w + ((m : ℕ) : ℂ)‖ := by
        have hshow : f m = ‖w - (-((m : ℕ) : ℂ))‖ := rfl
        rw [hshow, sub_neg_eq_add]
      have hfar : (2 : ℝ) ≤ f m := by
        rw [hdm_eq]
        have htri3 := norm_add_le (w + ((m : ℕ) : ℂ)) (-w)
        have heq : (w + ((m : ℕ) : ℂ)) + -w = ((m : ℕ) : ℂ) := by abel
        rw [heq, Complex.norm_natCast, norm_neg] at htri3
        linarith [hMB, hmB']
      linarith [hr1]
  have hDiffOn : DifferentiableOn ℂ Complex.Gamma (Metric.ball w r) := by
    intro s hs
    exact (Complex.differentiableAt_Gamma s (hball s hs)).differentiableWithinAt
  exact DifferentiableOn.analyticAt hDiffOn (Metric.ball_mem_nhds _ hr)

/-- **Analyticity of the digamma function.** The digamma function $\psi = \Gamma'/\Gamma$, where
$\Gamma$ is the complex Gamma function, is complex analytic at every $w \in \mathbb{C}$ that is
not a nonpositive integer. -/
theorem analyticAt_digamma (w : ℂ) (hw : ∀ m : ℕ, w ≠ -((m : ℕ) : ℂ)) :
    AnalyticAt ℂ Complex.digamma w := by
  have hG := analyticAt_Gamma w hw
  exact (AnalyticAt.deriv hG).div hG (Complex.Gamma_ne_zero hw)

/-- **Complex and real derivatives of Gamma agree on the positive reals.** For every real
$t > 0$, the derivative of the complex Gamma function at $t$ equals the derivative of the real
Gamma function at $t$. -/
theorem deriv_Gamma_ofReal (t : ℝ) (ht : 0 < t) :
    deriv Complex.Gamma (↑t) = ↑(deriv Real.Gamma t) := by
  have hU : ∀ m : ℕ, (↑t : ℂ) ≠ -(((m : ℕ)) : ℂ) := by
    intro m hcon
    have hcon2 : t = -((m : ℕ) : ℝ) := by
      have h := congrArg Complex.re hcon
      simpa using h
    have hle : t ≤ 0 := by
      rw [hcon2]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    linarith
  have hUr : ∀ m : ℕ, t ≠ -((m : ℕ) : ℝ) := by
    intro m hcon
    have hle : t ≤ 0 := by
      rw [hcon]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    linarith
  have hC := (Complex.differentiableAt_Gamma _ hU).hasDerivAt
  have hR := (Real.differentiableAt_Gamma hUr).hasDerivAt
  have hC' := hC.comp_ofReal
  have hR' := hR.ofReal_comp
  have heq : (fun y : ℝ => Complex.Gamma ↑y) =ᶠ[𝓝 t] (fun y => ↑(Real.Gamma y)) :=
    Filter.Eventually.of_forall fun y => Complex.Gamma_ofReal y
  have hC'' := hC'.congr_of_eventuallyEq heq.symm
  exact hC''.unique hR'

/-- **Absolute convergence of the trigamma series.** For every complex number $z$, the series
$\sum_{k \ge 0} \frac{1}{(z + k + 1)^2}$ converges absolutely, that is, the series of absolute
values $\sum_{k \ge 0} \left|\frac{1}{(z + k + 1)^2}\right|$ is summable, where a term whose
denominator vanishes is read as $0$.

Because of this convention no hypothesis excluding the poles $z = -(k + 1)$ is needed. -/
theorem summable_norm_one_div_add_nat_succ_sq (z : ℂ) :
    Summable (fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖) := by
  have hterm : (fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖)
      = (fun k : ℕ => (‖z + ((k + 1 : ℕ) : ℂ)‖ ^ 2)⁻¹) := by
    funext k
    rw [norm_div, norm_pow, norm_one, one_div]
  rw [hterm]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖z‖)
  have hbound : ∀ k : ℕ,
      (‖z + ((k + N + 1 : ℕ) : ℂ)‖ ^ 2)⁻¹ ≤ 4 * ((((k + N + 1 : ℕ) : ℝ) ^ 2))⁻¹ := by
    intro k
    have hKN : (2 : ℝ) * ‖z‖ ≤ ((k + N + 1 : ℕ) : ℝ) := by
      have h1 : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by
        apply Nat.cast_le.mpr
        omega
      linarith [hN]
    have hK1 : (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have hnormK : ‖(((k + N + 1 : ℕ)) : ℂ)‖ = ((k + N + 1 : ℕ) : ℝ) :=
      Complex.norm_natCast _
    have htri : ((k + N + 1 : ℕ) : ℝ) ≤ ‖z + (((k + N + 1 : ℕ)) : ℂ)‖ + ‖z‖ := by
      have h := norm_add_le (z + ((((k + N + 1 : ℕ))) : ℂ)) (-z)
      have heq : z + ((((k + N + 1 : ℕ))) : ℂ) + -z = ((((k + N + 1 : ℕ))) : ℂ) := by
        abel
      rw [heq, hnormK, norm_neg] at h
      exact h
    have hhalf : ((k + N + 1 : ℕ) : ℝ) / 2 ≤ ‖z + (((k + N + 1 : ℕ)) : ℂ)‖ := by
      linarith
    have hsq : (((k + N + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ ‖z + (((k + N + 1 : ℕ)) : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (by linarith)) hhalf 2
    have hinv : (‖z + (((k + N + 1 : ℕ)) : ℂ)‖ ^ 2)⁻¹
        ≤ ((((k + N + 1 : ℕ) : ℝ) / 2) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    have halg : ((((k + N + 1 : ℕ) : ℝ) / 2) ^ 2)⁻¹
        = 4 * ((((k + N + 1 : ℕ) : ℝ) ^ 2))⁻¹ := by
      field_simp
      ring
    rw [halg] at hinv
    exact hinv
  have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hshift0 := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) (N + 1)).mpr h2
  have hshift : Summable (fun k : ℕ => (((((k + (N + 1)) : ℕ)) : ℝ) ^ 2)⁻¹) := by
    simpa using hshift0
  have hnat : ∀ k : ℕ, k + N + 1 = k + (N + 1) := fun k => by omega
  have hmaj : Summable (fun k : ℕ => 4 * ((((k + N + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
    simp only [hnat]
    exact hshift.mul_left 4
  have htail : Summable (fun k : ℕ => (‖z + ((k + N + 1 : ℕ) : ℂ)‖ ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hbound hmaj
  apply (summable_nat_add_iff (f := fun m : ℕ => (‖z + ((m + 1 : ℕ) : ℂ)‖ ^ 2)⁻¹) N).mp
  simpa using htail

/-- The half-plane `Re s > 1` where the complex digamma series converges. -/
private def seriesDomain : Set ℂ := {s : ℂ | 1 < s.re}

/-- **Terms of the complex digamma series.** For $j \in \mathbb{N}$ and $s \in \mathbb{C}$, the
$j$-th term of the complex digamma series at $s$ is $\frac{1}{j+1} - \frac{1}{j+s}$, where
$1/0$ is read as $0$. -/
def digammaSeriesTerm (j : ℕ) (s : ℂ) : ℂ :=
  1 / ((j : ℂ) + 1) - 1 / ((j : ℂ) + s)

/-- **Complex digamma series.** For $s \in \mathbb{C}$, the digamma series function at $s$ is
$\sum_{j=0}^{\infty} \left(\frac{1}{j+1} - \frac{1}{j+s}\right)$, the sum of the terms of the
complex digamma series at $s$.

The value is taken to be $0$ when the series is not summable, and a term with $j + s = 0$ uses
$1/0 = 0$. -/
def digammaSeriesFun (s : ℂ) : ℂ := ∑' j : ℕ, digammaSeriesTerm j s

private lemma helper_seriesDomain_open : IsOpen seriesDomain := by
  have heq : seriesDomain = Complex.re ⁻¹' Set.Ioi 1 := rfl
  rw [heq]
  exact isOpen_Ioi.preimage Complex.continuous_re

private lemma helper_seriesDomain_convex : Convex ℝ seriesDomain :=
  convex_halfSpace_gt
    (LinearMap.isLinearMap_of_compatibleSMul ℝ Complex.reLm) 1

private lemma helper_seriesDomain_preconn : IsPreconnected seriesDomain :=
  helper_seriesDomain_convex.isPreconnected

private lemma helper_seriesTerm_re (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    (j : ℝ) + 1 ≤ ((j : ℂ) + s).re := by
  rw [Complex.add_re, Complex.natCast_re]
  have hs' : (1 : ℝ) < s.re := hs
  linarith

private lemma helper_seriesTerm_ne (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) : (j : ℂ) + s ≠ 0 := by
  have hpos : (0 : ℝ) < ((j : ℂ) + s).re := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hle := helper_seriesTerm_re j s hs
    linarith
  intro hcon
  have h0 := congrArg Complex.re hcon
  rw [Complex.zero_re] at h0
  linarith

private lemma helper_seriesTerm_hasDeriv (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    HasDerivAt (digammaSeriesTerm j) (1 / ((j : ℂ) + s) ^ 2) s := by
  have hne : s + (j : ℂ) ≠ 0 := by
    have h := helper_seriesTerm_ne j s hs
    rwa [add_comm] at h
  have hbase : HasDerivAt (fun t : ℂ => t + (j : ℂ)) 1 s :=
    (hasDerivAt_id' s).add_const ((j : ℂ))
  have hinv := hbase.inv hne
  have hsub := HasDerivAt.const_sub (1 / ((j : ℂ) + 1)) hinv
  simp only [Pi.inv_apply] at hsub
  have hfun : digammaSeriesTerm j
      = fun t : ℂ => 1 / ((j : ℂ) + 1) - (t + (j : ℂ))⁻¹ := by
    funext t
    simp [digammaSeriesTerm, one_div, add_comm]
  have hderiv : -(-1 / (s + (j : ℂ)) ^ 2)
      = 1 / ((j : ℂ) + s) ^ 2 := by
    rw [add_comm s ((j : ℂ))]
    ring
  rw [hfun, ← hderiv]
  exact hsub

private lemma helper_seriesDeriv_bound (j : ℕ) (s : ℂ)
    (hs : s ∈ seriesDomain) :
    ‖(1 / ((j : ℂ) + s) ^ 2 : ℂ)‖ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
  have hnorm : ((j : ℝ) + 1) ≤ ‖((j : ℂ) + s)‖ :=
    (helper_seriesTerm_re j s hs).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ ‖((j : ℂ) + s)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnorm 2
  rw [norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le (by positivity) hsq

private lemma helper_series_summable_at_two :
    Summable (fun j : ℕ => digammaSeriesTerm j 2) := by
  refine Summable.of_norm_bounded Real.summable_one_div_add_nat_succ_sq
    (fun j => ?_)
  have e1 : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
    simp [Complex.ofReal_add]
  have e2 : ((j : ℂ) + 2) = Complex.ofReal ((j : ℝ) + 2) := by
    simp [Complex.ofReal_add]
  have h1 : ((j : ℂ) + 1) ≠ 0 := by
    rw [e1]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
  have h2 : ((j : ℂ) + 2) ≠ 0 := by
    rw [e2]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 2 by positivity)
  have heq : digammaSeriesTerm j 2
      = 1 / (((j : ℂ) + 1) * ((j : ℂ) + 2)) := by
    simp only [digammaSeriesTerm, div_sub_div _ _ h1 h2, one_mul, mul_one]
    have hnum : ((j : ℂ) + 2) - ((j : ℂ) + 1) = 1 := by ring
    rw [hnum]
  rw [heq, norm_div, norm_one]
  have hle : ((j : ℝ) + 1) ^ 2
      ≤ ‖((j : ℂ) + 1) * ((j : ℂ) + 2)‖ := by
    rw [norm_mul, e1, e2, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 2 by positivity)]
    have h2le : (j : ℝ) + 1 ≤ (j : ℝ) + 2 := by linarith
    calc ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
      _ ≤ ((j : ℝ) + 1) * ((j : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left h2le (by positivity)
  exact one_div_le_one_div_of_le (by positivity) hle

private lemma helper_seriesFun_hasDeriv (s : ℂ)
    (hs : s ∈ seriesDomain) :
    HasDerivAt digammaSeriesFun
      (∑' j : ℕ, (1 / ((j : ℂ) + s) ^ 2 : ℂ)) s :=
  hasDerivAt_tsum_of_isPreconnected Real.summable_one_div_add_nat_succ_sq
    helper_seriesDomain_open helper_seriesDomain_preconn
    (fun j y hy => helper_seriesTerm_hasDeriv j y hy)
    (fun j y hy => helper_seriesDeriv_bound j y hy)
    (by
      change (1 : ℝ) < (2 : ℂ).re
      have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
      rw [h2c, Complex.ofReal_re]
      norm_num)
    helper_series_summable_at_two hs

private lemma helper_seriesFun_analytic :
    AnalyticOnNhd ℂ digammaSeriesFun seriesDomain :=
  DifferentiableOn.analyticOnNhd
    (fun s hs =>
      (helper_seriesFun_hasDeriv s hs).differentiableAt.differentiableWithinAt)
    helper_seriesDomain_open

private def digammaFun (s : ℂ) : ℂ :=
  Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)

private lemma helper_digammaFun_analytic :
    AnalyticOnNhd ℂ digammaFun seriesDomain := by
  intro s hs
  have hs' : (1 : ℝ) < s.re := hs
  have hw : ∀ m : ℕ, s ≠ -((m : ℕ) : ℂ) := by
    intro m hcon
    have h0 := congrArg Complex.re hcon
    rw [Complex.neg_re, Complex.natCast_re] at h0
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact (Complex.analyticAt_digamma s hw).add analyticAt_const

private lemma helper_series_agree_real (t : ℝ) (ht : 1 < t) :
    digammaFun (t : ℂ) = digammaSeriesFun (t : ℂ) := by
  have hx : (0 : ℝ) < t - 1 := by linarith
  have hsum := Real.hasSum_digamma_series (t - 1) hx
  rw [sub_add_cancel] at hsum
  have htsum := hsum.tsum_eq
  have hcast : ((∑' j : ℕ,
      (1 / ((j : ℝ) + 1) - 1 / ((t - 1) + (j : ℝ) + 1)) : ℝ) : ℂ)
      = digammaSeriesFun (t : ℂ) := by
    rw [Complex.ofReal_tsum]
    have hfun : (fun j : ℕ => (((1 / ((j : ℝ) + 1)
        - 1 / ((t - 1) + (j : ℝ) + 1)) : ℝ) : ℂ))
        = fun j : ℕ => digammaSeriesTerm j (t : ℂ) := by
      funext j
      have hden : Complex.ofReal ((t - 1) + (j : ℝ) + 1)
          = (j : ℂ) + (t : ℂ) := by
        push_cast
        ring
      have hden2 : Complex.ofReal ((j : ℝ) + 1) = (j : ℂ) + 1 := by
        simp [Complex.ofReal_add]
      simp only [digammaSeriesTerm, Complex.ofReal_sub, Complex.ofReal_div,
        Complex.ofReal_one, hden, hden2]
    rw [hfun]
    rfl
  have hval : ((deriv (fun u => Real.log (Real.Gamma u)) t
      + Real.eulerMascheroniConstant : ℝ) : ℂ)
      = digammaFun (t : ℂ) := by
    have ht0 : (0 : ℝ) < t := by linarith
    rw [Real.deriv_log_Gamma t ht0]
    simp only [digammaFun, Complex.digamma_def, logDeriv_apply,
      Complex.deriv_Gamma_ofReal t ht0, Complex.Gamma_ofReal,
      Complex.ofReal_div, Complex.ofReal_add]
  have htsumC := congrArg (fun r : ℝ => (r : ℂ)) htsum
  rw [hcast, hval] at htsumC
  exact htsumC.symm

private lemma helper_series_freq :
    ∃ᶠ z in 𝓝[≠] (2 : ℂ), digammaFun z = digammaSeriesFun z := by
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
  intro U hUmem hUopen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 2 hUmem
  set t : ℝ := 2 + min (ε / 2) (1 / 2) with htdef
  have hmin_pos : (0 : ℝ) < min (ε / 2) (1 / 2) :=
    lt_min (by linarith) (by norm_num)
  have ht2 : (2 : ℝ) < t := by rw [htdef]; linarith
  have ht1 : (1 : ℝ) < t := by linarith
  have hmin_lt : min (ε / 2) (1 / 2) < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  have hmem : ((t : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) ε := by
    rw [Metric.mem_ball, h2c, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 2)]
    rw [htdef]
    linarith
  refine ⟨(t : ℂ), hball hmem, ?_, ?_⟩
  · exact helper_series_agree_real t ht1
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [h2c]
    exact_mod_cast ne_of_gt ht2

private lemma helper_complex_digamma_series (s : ℂ)
    (hs : 1 < s.re) :
    Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)
      = digammaSeriesFun s := by
  have hmem2 : (2 : ℂ) ∈ seriesDomain := by
    change (1 : ℝ) < (2 : ℂ).re
    have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    rw [h2c, Complex.ofReal_re]
    norm_num
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    helper_digammaFun_analytic helper_seriesFun_analytic
    helper_seriesDomain_preconn hmem2 helper_series_freq
  have hmem : s ∈ seriesDomain := hs
  have h := heq hmem
  simpa [digammaFun] using h
/-- **Summability of the digamma series terms.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the sequence of digamma series terms
$\frac{1}{j+1} - \frac{1}{j+s}$, for $j = 0, 1, 2, \dots$, is summable. -/
theorem summable_digammaSeriesTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun j : ℕ => digammaSeriesTerm j s) := by
  have hmem : s ∈ seriesDomain := hs
  have hne1 : ∀ j : ℕ, ((j : ℂ) + 1) ≠ 0 := by
    intro j
    have e : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
      simp [Complex.ofReal_add]
    rw [e]
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
  have hnorm : ∀ j : ℕ, ((j : ℝ) + 1) ≤ ‖((j : ℂ) + s)‖ := fun j =>
    (helper_seriesTerm_re j s hmem).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hterm : ∀ j : ℕ, digammaSeriesTerm j s
      = (s - 1) / (((j : ℂ) + 1) * ((j : ℂ) + s)) := by
    intro j
    rw [digammaSeriesTerm, div_sub_div _ _ (hne1 j) (helper_seriesTerm_ne j s hmem)]
    congr 1
    ring
  have hbound : ∀ j : ℕ, ‖digammaSeriesTerm j s‖
      ≤ ‖s - 1‖ / ((j : ℝ) + 1) ^ 2 := by
    intro j
    rw [hterm j, norm_div, norm_mul]
    have h1 : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
      have e : ((j : ℂ) + 1) = Complex.ofReal ((j : ℝ) + 1) := by
        simp [Complex.ofReal_add]
      rw [e, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)]
    rw [h1]
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hle : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) * ‖((j : ℂ) + s)‖ := by
      have h := hnorm j
      calc ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) * ((j : ℝ) + 1) := by ring
        _ ≤ ((j : ℝ) + 1) * ‖((j : ℂ) + s)‖ :=
          mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle
  have hmaj : Summable (fun j : ℕ => ‖s - 1‖ / ((j : ℝ) + 1) ^ 2) := by
    have e : (fun j : ℕ => ‖s - 1‖ / ((j : ℝ) + 1) ^ 2)
        = fun j : ℕ => ‖s - 1‖ * (1 / ((j : ℝ) + 1) ^ 2) := by
      funext j
      ring
    rw [e]
    exact Real.summable_one_div_add_nat_succ_sq.mul_left _
  exact Summable.of_norm_bounded hmaj hbound

/-- **Series expansion of the complex digamma function.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the series
$\sum_{j=0}^{\infty} \left(\frac{1}{j+1} - \frac{1}{j+s}\right)$ of the terms of the complex
digamma series at $s$ has sum $\psi(s) + \gamma$, where $\psi = \Gamma'/\Gamma$ is the complex
digamma function, the logarithmic derivative of the complex Gamma function, and $\gamma$ is the
Euler–Mascheroni constant. -/
theorem hasSum_digamma_series (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => digammaSeriesTerm j s)
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by
  have hsum := summable_digammaSeriesTerm s hs
  have heq := helper_complex_digamma_series s hs
  rw [heq]
  exact hsum.hasSum

end Complex

end
