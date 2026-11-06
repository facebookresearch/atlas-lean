/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 16

Infinite sum of rᵏ/(1-axᵏ) splits into two related convergent series.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry16InfiniteSum

open scoped Nat Real BigOperators Interval Polynomial
open Asymptotics Filter Finset Complex Topology

noncomputable section

def chapter6Entry16LeftTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  r ^ k / (1 - a * x ^ k)

def chapter6Entry16MiddleTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  (a * r * x ^ k) ^ k / (1 - a * x ^ k)

def chapter6Entry16RightTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  a ^ (k - 1) * r ^ k * x ^ ((k - 1) * k) /
    (1 - r * x ^ (k - 1))

/-- Triangle summand for the double-sum argument:
`triFun a r x n m = a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n)` on `n ≤ m`. -/
private def triFun (a r x : ℂ) (n m : ℕ) : ℂ :=
  if n ≤ m then a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n) else 0

/-- Uniform majorant for the column sums. -/
private def triBound (a r x : ℂ) (n : ℕ) : ℝ :=
  ‖r‖ / (1 - ‖r‖) * (‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1)) ^ n

private lemma triBound_nonneg (a r x : ℂ) (hr : ‖r‖ < 1) (n : ℕ) :
    0 ≤ triBound a r x n := by
  unfold triBound
  apply mul_nonneg
  · exact div_nonneg (norm_nonneg _) (sub_nonneg.mpr hr.le)
  · exact pow_nonneg (by positivity) _

private lemma rightDenom_ne {r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1)
    (k : ℕ) (_hk : 1 ≤ k) : 1 - r * x ^ (k - 1) ≠ 0 := by
  intro h
  have h1 : r * x ^ (k - 1) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖r * x ^ (k - 1)‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, norm_pow] at hnorm
  have hxpow : ‖x‖ ^ (k - 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
  have hle : ‖r‖ * ‖x‖ ^ (k - 1) ≤ ‖r‖ := by
    calc ‖r‖ * ‖x‖ ^ (k - 1) ≤ ‖r‖ * 1 :=
          mul_le_mul_of_nonneg_left hxpow (norm_nonneg _)
    _ = ‖r‖ := mul_one _
  linarith

private lemma norm_rx_lt {r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖r * x ^ m‖ < 1 := by
  rw [norm_mul, norm_pow]
  calc ‖r‖ * ‖x‖ ^ m ≤ ‖r‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
  _ = ‖r‖ := mul_one _
  _ < 1 := hr

private lemma summable_real_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => q ^ n) := by
  have h : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  exact summable_geometric_of_norm_lt_one h

private lemma summable_const_mul_real_geometric {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => C * q ^ n) :=
  (summable_real_geometric hq0 hq1).mul_left C

private lemma summable_shifted_geometric {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => C * q ^ (j + 1)) := by
  have hgeo : Summable (fun j : ℕ => (C * q) * q ^ j) :=
    (summable_real_geometric hq0 hq1).mul_left _
  have heq : (fun j : ℕ => C * q ^ (j + 1)) = (fun j : ℕ => (C * q) * q ^ j) := by
    funext j
    rw [pow_succ]
    ring
  rwa [heq]

private lemma one_sub_norm_le {z : ℂ} : 1 - ‖z‖ ≤ ‖1 - z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) z
  rwa [norm_one] at h

private lemma half_le_denom_of_small {a x : ℂ} {k : ℕ}
    (h : ‖a * x ^ k‖ ≤ 1 / 2) : 1 / 2 ≤ ‖1 - a * x ^ k‖ := by
  have h1 : (1 : ℝ) - ‖a * x ^ k‖ ≤ ‖1 - a * x ^ k‖ := one_sub_norm_le
  linarith

private lemma tendsto_ax_pow {a x : ℂ} (hxlt : ‖x‖ < 1) :
    Filter.Tendsto (fun k : ℕ => a * x ^ k) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k : ℕ => x ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hxlt
  have hconst : Filter.Tendsto (fun _ : ℕ => a) Filter.atTop (nhds a) :=
    tendsto_const_nhds
  simpa using hconst.mul h

private lemma eventually_norm_ax_le_half {a x : ℂ} (hxlt : ‖x‖ < 1) :
    ∀ᶠ k : ℕ in Filter.atTop, ‖a * x ^ k‖ ≤ 1 / 2 := by
  have hlim : Filter.Tendsto (fun k : ℕ => ‖a * x ^ k‖) Filter.atTop (nhds 0) := by
    have h := tendsto_ax_pow (a := a) hxlt
    simpa using h.norm
  have hlt := (tendsto_order.mp hlim).2 (1 / 2) (show (1 / 2 : ℝ) > 0 by norm_num)
  exact hlt.mono fun k hk => hk.le

private lemma eventually_cofinite_of_atTop {p : ℕ → Prop}
    (h : ∀ᶠ k : ℕ in Filter.atTop, p k) : ∀ᶠ k : ℕ in Filter.cofinite, p k := by
  rwa [Nat.cofinite_eq_atTop]

/-- Divide a norm bound by a denominator bounded below. -/
private lemma div_norm_le_of_denom_le {N D d : ℝ} (hN : 0 ≤ N) (hDd : d ≤ D)
    (hd0 : 0 < d) : N / D ≤ d⁻¹ * N := by
  have hD : 0 < D := lt_of_lt_of_le hd0 hDd
  have h4 : D⁻¹ ≤ d⁻¹ := (inv_le_inv₀ hD hd0).mpr hDd
  calc N / D = N * D⁻¹ := div_eq_mul_inv _ _
  _ ≤ N * d⁻¹ := mul_le_mul_of_nonneg_left h4 hN
  _ = d⁻¹ * N := mul_comm _ _

private lemma summable_left_of_denom_bound {a r x : ℂ} (hr : ‖r‖ < 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : ∀ k : ℕ, 1 ≤ k → δ ≤ ‖1 - a * x ^ k‖) :
    Summable (chapter6Entry16LeftTerm a r x) := by
  apply Summable.of_norm_bounded (g := fun j : ℕ => δ⁻¹ * ‖r‖ ^ (j + 1))
  · exact summable_shifted_geometric (norm_nonneg _) hr
  · intro j
    show ‖r ^ (j + 1) / (1 - a * x ^ (j + 1))‖ ≤ δ⁻¹ * ‖r‖ ^ (j + 1)
    rw [norm_div, norm_pow]
    exact div_norm_le_of_denom_le (pow_nonneg (norm_nonneg _) _) (hδ _ (by omega)) hδ0

private lemma summable_middle_of_boundary {a r x : ℂ} (har : ‖a‖ * ‖r‖ < 1)
    (hξ1 : ‖x‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : ∀ k : ℕ, 1 ≤ k → δ ≤ ‖1 - a * x ^ k‖) :
    Summable (chapter6Entry16MiddleTerm a r x) := by
  have har0 : 0 ≤ ‖a‖ * ‖r‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  apply Summable.of_norm_bounded (g := fun j : ℕ => δ⁻¹ * (‖a‖ * ‖r‖) ^ (j + 1))
  · exact summable_shifted_geometric har0 har
  · intro j
    show ‖(a * r * x ^ (j + 1)) ^ (j + 1) / (1 - a * x ^ (j + 1))‖ ≤ _
    simp only [norm_div, norm_pow, norm_mul, hξ1, one_pow, mul_one]
    exact div_norm_le_of_denom_le (pow_nonneg har0 _) (hδ _ (by omega)) hδ0

private lemma summable_right_of_boundary {a r x : ℂ} (hr : ‖r‖ < 1)
    (har : ‖a‖ * ‖r‖ < 1) (hξ1 : ‖x‖ = 1) :
    Summable (chapter6Entry16RightTerm a r x) := by
  have h1ρ : (0 : ℝ) < 1 - ‖r‖ := sub_pos.mpr hr
  have har0 : 0 ≤ ‖a‖ * ‖r‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  apply Summable.of_norm_bounded
    (g := fun j : ℕ => (‖r‖ / (1 - ‖r‖)) * (‖a‖ * ‖r‖) ^ j)
  · exact (summable_real_geometric har0 har).mul_left _
  · intro j
    show ‖a ^ (j + 1 - 1) * r ^ (j + 1) * x ^ ((j + 1 - 1) * (j + 1)) /
        (1 - r * x ^ (j + 1 - 1))‖ ≤ _
    rw [Nat.add_sub_cancel]
    have hD : (1 : ℝ) - ‖r‖ ≤ ‖1 - r * x ^ j‖ := by
      have h1 := one_sub_norm_le (z := r * x ^ j)
      have h2x : ‖r * x ^ j‖ ≤ ‖r‖ := by
        simp only [norm_mul, norm_pow, hξ1, one_pow, mul_one, le_rfl]
      linarith
    simp only [norm_div, norm_mul, norm_pow, hξ1, one_pow, mul_one]
    have hN0 : (0 : ℝ) ≤ ‖a‖ ^ j * ‖r‖ ^ (j + 1) :=
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
    have hN := div_norm_le_of_denom_le hN0 hD h1ρ
    have hring : (1 - ‖r‖)⁻¹ * (‖a‖ ^ j * ‖r‖ ^ (j + 1))
        = (‖r‖ / (1 - ‖r‖)) * (‖a‖ * ‖r‖) ^ j := by
      rw [div_eq_mul_inv]
      ring
    exact hN.trans (le_of_eq hring)

private lemma summable_left_of_interior {a r x : ℂ} (hr : ‖r‖ < 1)
    (hev : ∀ᶠ k : ℕ in Filter.atTop, ‖a * x ^ k‖ ≤ 1 / 2) :
    Summable (chapter6Entry16LeftTerm a r x) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have h2 : ∀ᶠ j : ℕ in Filter.atTop, ‖a * x ^ (j + 1)‖ ≤ 1 / 2 :=
    Filter.eventually_atTop.mpr ⟨N, fun j _ => hN (j + 1) (by omega)⟩
  apply Summable.of_norm_bounded_eventually (g := fun j : ℕ => 2 * ‖r‖ ^ (j + 1))
  · exact summable_shifted_geometric (norm_nonneg _) hr
  · have h1 := eventually_cofinite_of_atTop h2
    filter_upwards [h1] with j hj
    show ‖r ^ (j + 1) / (1 - a * x ^ (j + 1))‖ ≤ 2 * ‖r‖ ^ (j + 1)
    rw [norm_div, norm_pow]
    have hD := half_le_denom_of_small hj
    have hN : (0 : ℝ) ≤ ‖r‖ ^ (j + 1) := pow_nonneg (norm_nonneg _) _
    have h := div_norm_le_of_denom_le hN
      hD (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2eq : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    rw [h2eq] at h
    exact h

private lemma summable_middle_of_interior {a r x : ℂ} (hr : ‖r‖ < 1)
    (hev : ∀ᶠ k : ℕ in Filter.atTop, ‖a * x ^ k‖ ≤ 1 / 2) :
    Summable (chapter6Entry16MiddleTerm a r x) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hboth : ∀ᶠ j : ℕ in Filter.atTop,
      ‖a * x ^ (j + 1)‖ ≤ 1 / 2 ∧ ‖a * r * x ^ (j + 1)‖ ≤ 1 / 2 := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun j hj => ⟨hN _ (by omega), ?_⟩⟩
    have hjt := hN (j + 1) (by omega)
    have e : a * r * x ^ (j + 1) = r * (a * x ^ (j + 1)) := by ring
    rw [e, norm_mul]
    calc ‖r‖ * ‖a * x ^ (j + 1)‖ ≤ 1 * (1 / 2) :=
          mul_le_mul (le_of_lt hr) hjt (norm_nonneg _) (by norm_num)
    _ = 1 / 2 := one_mul _
  apply Summable.of_norm_bounded_eventually (g := fun j : ℕ => 2 * (1 / 2 : ℝ) ^ (j + 1))
  · exact summable_shifted_geometric (by norm_num) (by norm_num)
  · have h1 := eventually_cofinite_of_atTop hboth
    filter_upwards [h1] with j hj
    obtain ⟨hj1, hj2⟩ := hj
    show ‖(a * r * x ^ (j + 1)) ^ (j + 1) / (1 - a * x ^ (j + 1))‖ ≤ _
    simp only [norm_div, norm_pow]
    have hD := half_le_denom_of_small hj1
    have hnum : ‖a * r * x ^ (j + 1)‖ ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hj2 _
    have hN : (0 : ℝ) ≤ ‖a * r * x ^ (j + 1)‖ ^ (j + 1) :=
      pow_nonneg (norm_nonneg _) _
    have h := div_norm_le_of_denom_le hN
      hD (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2eq : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    calc ‖a * r * x ^ (j + 1)‖ ^ (j + 1) / ‖1 - a * x ^ (j + 1)‖
        ≤ ((1 / 2 : ℝ))⁻¹ * ‖a * r * x ^ (j + 1)‖ ^ (j + 1) := h
      _ ≤ ((1 / 2 : ℝ))⁻¹ * (1 / 2 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ = 2 * (1 / 2 : ℝ) ^ (j + 1) := by rw [h2eq]

private lemma summable_right_of_interior {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1)
    (hev : ∀ᶠ k : ℕ in Filter.atTop, ‖a * x ^ k‖ ≤ 1 / 2) :
    Summable (chapter6Entry16RightTerm a r x) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have h1ρ : (0 : ℝ) < 1 - ‖r‖ := sub_pos.mpr hr
  apply Summable.of_norm_bounded_eventually
    (g := fun j : ℕ => (‖r‖ / (1 - ‖r‖)) * (1 / 2 : ℝ) ^ j)
  · exact (summable_real_geometric (by norm_num) (by norm_num)).mul_left _
  · have h2 : ∀ᶠ j : ℕ in Filter.atTop, ‖a * x ^ (j + 1)‖ ≤ 1 / 2 :=
      Filter.eventually_atTop.mpr ⟨N, fun j _ => hN (j + 1) (by omega)⟩
    have h1 := eventually_cofinite_of_atTop h2
    filter_upwards [h1] with j hj
    show ‖a ^ (j + 1 - 1) * r ^ (j + 1) * x ^ ((j + 1 - 1) * (j + 1)) /
        (1 - r * x ^ (j + 1 - 1))‖ ≤ (‖r‖ / (1 - ‖r‖)) * (1 / 2 : ℝ) ^ j
    rw [Nat.add_sub_cancel, norm_div]
    have hD : (1 : ℝ) - ‖r‖ ≤ ‖1 - r * x ^ j‖ := by
      have h1l := one_sub_norm_le (z := r * x ^ j)
      have h2x : ‖r * x ^ j‖ ≤ ‖r‖ := by
        rw [norm_mul, norm_pow]
        calc ‖r‖ * ‖x‖ ^ j ≤ ‖r‖ * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
        _ = ‖r‖ := mul_one _
      linarith
    have hnum : ‖a ^ j * r ^ (j + 1) * x ^ (j * (j + 1))‖
        ≤ ‖r‖ * (1 / 2 : ℝ) ^ j := by
      have hsj : ‖a‖ * ‖r‖ * ‖x‖ ^ (j + 1) ≤ 1 / 2 := by
        have e : ‖a‖ * ‖r‖ * ‖x‖ ^ (j + 1) = ‖r‖ * ‖a * x ^ (j + 1)‖ := by
          rw [norm_mul, norm_pow]
          ring
        rw [e]
        calc ‖r‖ * ‖a * x ^ (j + 1)‖ ≤ 1 * (1 / 2) :=
              mul_le_mul (le_of_lt hr) hj (norm_nonneg _) (by norm_num)
        _ = 1 / 2 := one_mul _
      have hbase : (0 : ℝ) ≤ ‖a‖ * ‖r‖ * ‖x‖ ^ (j + 1) := by positivity
      have hpow : (‖a‖ * ‖r‖ * ‖x‖ ^ (j + 1)) ^ j ≤ (1 / 2 : ℝ) ^ j :=
        pow_le_pow_left₀ hbase hsj _
      have heq : ‖a‖ ^ j * ‖r‖ ^ (j + 1) * ‖x‖ ^ (j * (j + 1))
          = ‖r‖ * (‖a‖ * ‖r‖ * ‖x‖ ^ (j + 1)) ^ j := by ring
      simp only [norm_mul, norm_pow]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    have hN0 : (0 : ℝ) ≤ ‖a ^ j * r ^ (j + 1) * x ^ (j * (j + 1))‖ :=
      norm_nonneg _
    have h := div_norm_le_of_denom_le hN0 hD h1ρ
    have h2b : (1 - ‖r‖)⁻¹ * ‖a ^ j * r ^ (j + 1) * x ^ (j * (j + 1))‖
        ≤ (‖r‖ / (1 - ‖r‖)) * (1 / 2 : ℝ) ^ j := by
      have hmul := mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr h1ρ.le)
      rw [div_eq_mul_inv]
      calc (1 - ‖r‖)⁻¹ * ‖a ^ j * r ^ (j + 1) * x ^ (j * (j + 1))‖
          ≤ (1 - ‖r‖)⁻¹ * (‖r‖ * (1 / 2 : ℝ) ^ j) := hmul
        _ = ‖r‖ / (1 - ‖r‖) * (1 / 2 : ℝ) ^ j := by
            rw [div_eq_mul_inv]
            ring
    exact h.trans h2b

private lemma summable_uncurry_of_fiber_bounds {F : ℕ → ℕ → ℂ} {g : ℕ → ℝ}
    (hg0 : ∀ n, 0 ≤ g n)
    (hfiber : ∀ n, Summable (fun m => ‖F n m‖))
    (hbound : ∀ n, ∑' m, ‖F n m‖ ≤ g n)
    (hg : Summable g) :
    Summable (Function.uncurry F) := by
  apply Summable.of_norm
  have hG' : Summable (fun p : ℕ × ℕ => ‖F p.1 p.2‖) := by
    rw [← Equiv.summable_iff (Denumerable.eqv (ℕ × ℕ)).symm]
    apply summable_of_sum_range_le
    · intro n
      exact norm_nonneg _
    · intro N
      simp only [Function.comp_apply]
      let e := (Denumerable.eqv (ℕ × ℕ)).symm
      let Fset := (Finset.range N).image (fun i => (e i).1)
      let Gset := (Finset.range N).image (fun i => (e i).2)
      have hsub : (Finset.range N).image (fun i => e i) ⊆ Fset ×ˢ Gset := by
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        rw [Finset.mem_product]
        exact ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩,
          Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
      calc ∑ i ∈ Finset.range N, ‖F (e i).1 (e i).2‖
          = ∑ p ∈ (Finset.range N).image (fun i => e i), ‖F p.1 p.2‖ :=
            (Finset.sum_image (f := fun p : ℕ × ℕ => ‖F p.1 p.2‖)
              (g := fun i => e i) (s := Finset.range N)
              (fun x _ y _ hxy => e.injective hxy)).symm
        _ ≤ ∑ p ∈ Fset ×ˢ Gset, ‖F p.1 p.2‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
        _ = ∑ n ∈ Fset, ∑ m ∈ Gset, ‖F n m‖ :=
            Finset.sum_product _ _ _
        _ ≤ ∑ n ∈ Fset, ∑' m, ‖F n m‖ := by
            apply Finset.sum_le_sum
            intro n _
            exact Summable.sum_le_tsum _ (fun i _ => norm_nonneg _) (hfiber n)
        _ ≤ ∑ n ∈ Fset, g n :=
            Finset.sum_le_sum (fun n _ => hbound n)
        _ ≤ ∑' n, g n :=
            Summable.sum_le_tsum _ (fun i _ => hg0 i) hg
  exact hG'

private lemma fiber_summable {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1)
    (n : ℕ) : Summable (fun m => triFun a r x n m) := by
  apply Summable.of_norm_bounded (g := fun m : ℕ => (‖a‖ ^ n * ‖r‖) * ‖r‖ ^ m)
  · exact (summable_real_geometric (norm_nonneg _) hr).mul_left _
  · intro m
    unfold triFun
    by_cases h : n ≤ m
    · rw [ite_eq_left h]
      simp only [norm_mul, norm_pow]
      have hξ : ‖x‖ ^ ((m + 1) * n) ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
      have hnn : (0 : ℝ) ≤ ‖a‖ ^ n * ‖r‖ ^ (m + 1) := by positivity
      have hle : ‖a‖ ^ n * ‖r‖ ^ (m + 1) * ‖x‖ ^ ((m + 1) * n)
          ≤ ‖a‖ ^ n * ‖r‖ ^ (m + 1) * 1 :=
        mul_le_mul_of_nonneg_left hξ hnn
      have heq : ‖a‖ ^ n * ‖r‖ ^ (m + 1) * 1
          = (‖a‖ ^ n * ‖r‖) * ‖r‖ ^ m := by
        rw [pow_succ]
        ring
      exact hle.trans (le_of_eq heq)
    · rw [ite_eq_right h, norm_zero]
      exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)

private lemma fiber_norm_summable {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1)
    (n : ℕ) : Summable (fun m => ‖triFun a r x n m‖) :=
  (fiber_summable hr hx n).norm

private lemma hasSum_geometric_tail {K : Type*} [NormedDivisionRing K] {z : K}
    (hz : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => (if n ≤ m then z ^ (m - n) else (0 : K))) (1 - z)⁻¹ := by
  have hgeo : HasSum (fun k : ℕ => z ^ k) (1 - z)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hz
  have heq : (fun m : ℕ => (if n ≤ m + n then z ^ (m + n - n) else (0 : K)))
      = (fun k : ℕ => z ^ k) := by
    funext m
    show (if n ≤ m + n then z ^ (m + n - n) else (0 : K)) = z ^ m
    rw [ite_eq_left (Nat.le_add_left n m), Nat.add_sub_cancel]
  have hshifted : HasSum
      (fun m : ℕ => (if n ≤ m + n then z ^ (m + n - n) else (0 : K))) (1 - z)⁻¹ := by
    rw [heq]
    exact hgeo
  have hmain := (hasSum_nat_add_iff
    (f := fun m : ℕ => (if n ≤ m then z ^ (m - n) else (0 : K))) n).mp hshifted
  have hzero : ∑ i ∈ Finset.range n, (if n ≤ i then z ^ (i - n) else (0 : K)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [ite_eq_right (by omega)]
  rw [hzero, add_zero] at hmain
  exact hmain

private lemma column_tsum {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∑' m, triFun a r x n m = chapter6Entry16RightTerm a r x n := by
  have hz : ‖r * x ^ n‖ < 1 := norm_rx_lt hr hx n
  have htail := hasSum_geometric_tail hz n
  have hmul := HasSum.mul_left (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) htail
  have hfg : (fun m : ℕ => (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) *
        (if n ≤ m then (r * x ^ n) ^ (m - n) else (0 : ℂ)))
      = (fun m => triFun a r x n m) := by
    funext m
    show (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) *
        (if n ≤ m then (r * x ^ n) ^ (m - n) else (0 : ℂ))
      = triFun a r x n m
    unfold triFun
    by_cases h : n ≤ m
    · rw [ite_eq_left h, ite_eq_left h]
      have e1 : n + 1 + (m - n) = m + 1 := by omega
      have e2 : n * (n + 1) + n * (m - n) = (m + 1) * n := by
        calc n * (n + 1) + n * (m - n) = n * ((n + 1) + (m - n)) := by ring
          _ = n * (m + 1) := by rw [show (n + 1) + (m - n) = m + 1 by omega]
          _ = (m + 1) * n := mul_comm _ _
      calc (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) * (r * x ^ n) ^ (m - n)
          = (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) *
            (r ^ (m - n) * (x ^ n) ^ (m - n)) := by rw [mul_pow]
        _ = a ^ n * (r ^ (n + 1) * r ^ (m - n)) *
            (x ^ (n * (n + 1)) * (x ^ n) ^ (m - n)) := by ring
        _ = a ^ n * r ^ (n + 1 + (m - n)) *
            x ^ (n * (n + 1) + n * (m - n)) := by rw [← pow_add, ← pow_mul, ← pow_add]
        _ = a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n) := by rw [e1, e2]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [hfg] at hmul
  have hval := hmul.tsum_eq
  have hR : chapter6Entry16RightTerm a r x n
      = (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) * (1 - r * x ^ n)⁻¹ := by
    show a ^ (n + 1 - 1) * r ^ (n + 1) * x ^ ((n + 1 - 1) * (n + 1)) /
        (1 - r * x ^ (n + 1 - 1))
      = (a ^ n * r ^ (n + 1) * x ^ (n * (n + 1))) * (1 - r * x ^ n)⁻¹
    rw [Nat.add_sub_cancel, div_eq_mul_inv]
  rw [hR]
  exact hval

private lemma column_norm_tsum {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∑' m, ‖triFun a r x n m‖
      = (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) * (1 - ‖r * x ^ n‖)⁻¹ := by
  have hz : ‖r * x ^ n‖ < 1 := norm_rx_lt hr hx n
  have hzR : ‖(‖r * x ^ n‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hz
  have htail := hasSum_geometric_tail hzR n
  have hmul := HasSum.mul_left
    (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) htail
  have hfg : (fun m : ℕ => (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) *
        (if n ≤ m then (‖r * x ^ n‖) ^ (m - n) else (0 : ℝ)))
      = (fun m => ‖triFun a r x n m‖) := by
    funext m
    show (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) *
        (if n ≤ m then (‖r * x ^ n‖) ^ (m - n) else (0 : ℝ))
      = ‖triFun a r x n m‖
    unfold triFun
    by_cases h : n ≤ m
    · rw [ite_eq_left h, ite_eq_left h]
      have hz2 : ‖r * x ^ n‖ ^ (m - n)
          = ‖r‖ ^ (m - n) * ‖x‖ ^ (n * (m - n)) := by
        rw [norm_mul, norm_pow, mul_pow, ← pow_mul]
      have e1 : n + 1 + (m - n) = m + 1 := by omega
      have e2 : n * (n + 1) + n * (m - n) = n * (m + 1) := by
        calc n * (n + 1) + n * (m - n) = n * ((n + 1) + (m - n)) := by ring
          _ = n * (m + 1) := by rw [show (n + 1) + (m - n) = m + 1 by omega]
      calc (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) * ‖r * x ^ n‖ ^ (m - n)
          = (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) *
            (‖r‖ ^ (m - n) * ‖x‖ ^ (n * (m - n))) := by rw [hz2]
        _ = ‖a‖ ^ n * (‖r‖ ^ (n + 1) * ‖r‖ ^ (m - n)) *
            (‖x‖ ^ (n * (n + 1)) * ‖x‖ ^ (n * (m - n))) := by ring
        _ = ‖a‖ ^ n * ‖r‖ ^ (n + 1 + (m - n)) *
            ‖x‖ ^ (n * (n + 1) + n * (m - n)) := by rw [← pow_add, ← pow_add]
        _ = ‖a‖ ^ n * ‖r‖ ^ (m + 1) * ‖x‖ ^ (n * (m + 1)) := by rw [e1, e2]
        _ = ‖a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n)‖ := by
            rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
              mul_comm n (m + 1)]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, norm_zero]
  rw [hfg] at hmul
  exact hmul.tsum_eq

private lemma column_le_bound {a r x : ℂ} (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∑' m, ‖triFun a r x n m‖ ≤ triBound a r x n := by
  have h1ρ : (0 : ℝ) < 1 - ‖r‖ := sub_pos.mpr hr
  have h1z : (0 : ℝ) < 1 - ‖r * x ^ n‖ := sub_pos.mpr (norm_rx_lt hr hx n)
  have hz_le : ‖r * x ^ n‖ ≤ ‖r‖ := by
    rw [norm_mul, norm_pow]
    calc ‖r‖ * ‖x‖ ^ n ≤ ‖r‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hx) (norm_nonneg _)
    _ = ‖r‖ := mul_one _
  have hK : (0 : ℝ) ≤ ‖a‖ ^ n * ‖r‖ ^ n * ‖x‖ ^ (n * (n + 1)) := by positivity
  have hinv : (1 - ‖r * x ^ n‖)⁻¹ ≤ (1 - ‖r‖)⁻¹ :=
    (inv_le_inv₀ h1z h1ρ).mpr (by linarith)
  have es : (‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1)) ^ n
      = ‖a‖ ^ n * ‖r‖ ^ n * ‖x‖ ^ (n * (n + 1)) := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm (n + 1) n]
  have goal_eq : (‖a‖ ^ n * ‖r‖ ^ (n + 1) * ‖x‖ ^ (n * (n + 1))) * (1 - ‖r * x ^ n‖)⁻¹
      = (‖a‖ ^ n * ‖r‖ ^ n * ‖x‖ ^ (n * (n + 1))) * (‖r‖ * (1 - ‖r * x ^ n‖)⁻¹) := by
    ring
  have tb_eq : triBound a r x n
      = (‖a‖ ^ n * ‖r‖ ^ n * ‖x‖ ^ (n * (n + 1))) * (‖r‖ * (1 - ‖r‖)⁻¹) := by
    rw [show triBound a r x n
      = (‖r‖ / (1 - ‖r‖)) * (‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1)) ^ n from rfl]
    rw [es, div_eq_mul_inv]
    ring
  rw [column_norm_tsum hr hx n, tb_eq, goal_eq]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hinv (norm_nonneg _)) hK

private lemma row_tsum {a r x : ℂ}
    (hpoles : ∀ k : ℕ, 1 ≤ k → 1 - a * x ^ k ≠ 0) (m : ℕ) :
    ∑' n, triFun a r x n m
      = chapter6Entry16LeftTerm a r x m - chapter6Entry16MiddleTerm a r x m := by
  have hsupp : ∀ b ∉ Finset.range (m + 1), triFun a r x b m = 0 := by
    intro b hb
    unfold triFun
    rw [Finset.mem_range] at hb
    rw [ite_eq_right (by omega)]
  rw [tsum_eq_sum hsupp]
  have hval : ∑ n ∈ Finset.range (m + 1), triFun a r x n m
      = r ^ (m + 1) * ∑ n ∈ Finset.range (m + 1), (a * x ^ (m + 1)) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    unfold triFun
    rw [ite_eq_left (by omega : n ≤ m), mul_pow]
    ring
  have hA : (1 : ℂ) - a * x ^ (m + 1) ≠ 0 := hpoles _ (by omega)
  have hgeom := geom_sum_mul (a * x ^ (m + 1)) (m + 1)
  have hS : ∑ n ∈ Finset.range (m + 1), (a * x ^ (m + 1)) ^ n
      = (1 - (a * x ^ (m + 1)) ^ (m + 1)) / (1 - a * x ^ (m + 1)) := by
    rw [eq_div_iff hA]
    linear_combination -hgeom
  rw [hval, hS, ← mul_div_assoc]
  show r ^ (m + 1) * (1 - (a * x ^ (m + 1)) ^ (m + 1)) / (1 - a * x ^ (m + 1))
    = (r ^ (m + 1) / (1 - a * x ^ (m + 1))
      - (a * r * x ^ (m + 1)) ^ (m + 1) / (1 - a * x ^ (m + 1)))
  rw [← sub_div]
  congr 1
  have hmid : (a * r * x ^ (m + 1)) ^ (m + 1)
      = r ^ (m + 1) * (a * x ^ (m + 1)) ^ (m + 1) := by ring
  rw [hmid]
  ring

private lemma fubini_step {a r x : ℂ}
    (hL : Summable (chapter6Entry16LeftTerm a r x))
    (hM : Summable (chapter6Entry16MiddleTerm a r x))
    (_hR : Summable (chapter6Entry16RightTerm a r x))
    (hpair : Summable (Function.uncurry (triFun a r x)))
    (hrow : ∀ m, ∑' n, triFun a r x n m
      = chapter6Entry16LeftTerm a r x m - chapter6Entry16MiddleTerm a r x m)
    (hcol : ∀ n, ∑' m, triFun a r x n m
      = chapter6Entry16RightTerm a r x n) :
    ∑' j, chapter6Entry16LeftTerm a r x j
      = (∑' j, chapter6Entry16MiddleTerm a r x j)
        + ∑' j, chapter6Entry16RightTerm a r x j := by
  have hcomm := Summable.tsum_comm hpair
  simp only [hrow, hcol] at hcomm
  have hsub := Summable.tsum_sub hL hM
  rw [hsub] at hcomm
  linear_combination hcomm

/-- **Ramanujan's infinite identity for $\sum_k r^k/(1-ax^k)$.** Let $a, r, x$ be complex
numbers with $|r| < 1$ and $|x| \le 1$ such that $1 - a x^k \ne 0$ for every integer $k \ge 1$,
and such that, if $|x| = 1$, then $|a r| < 1$ and there is a real $\delta > 0$ with
$|1 - a x^k| \ge \delta$ for every $k \ge 1$. Then $1 - r x^{k-1} \ne 0$ for every $k \ge 1$, the
three series $\sum_{k=1}^{\infty} \frac{r^k}{1 - a x^k}$,
$\sum_{k=1}^{\infty} \frac{(a r x^k)^k}{1 - a x^k}$ and
$\sum_{k=1}^{\infty} \frac{a^{k-1} r^k x^{(k-1)k}}{1 - r x^{k-1}}$ are summable, and the first
equals the sum of the other two.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
The infinite form of `Entry16FiniteSum.ramanujan_part1_ch6_entry16_finite_sum`.
Proves `Wanted` entry `ramanujan_part1_ch6_entry9_centralbinomialasymptotic`.
-/
theorem ramanujan_part1_ch6_entry16_infinite_sum
    (a r x : ℂ)
    (hr : ‖r‖ < 1) (hx : ‖x‖ ≤ 1)
    (hboundary : ‖x‖ = 1 → ‖a * r‖ < 1)
    (hpoles : ∀ k : ℕ, 1 ≤ k → 1 - a * x ^ k ≠ 0)
    (hboundarySeparated : ‖x‖ = 1 →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ k : ℕ, 1 ≤ k → delta ≤ ‖1 - a * x ^ k‖) :
    (∀ k : ℕ, 1 ≤ k → 1 - r * x ^ (k - 1) ≠ 0) ∧
      Summable (chapter6Entry16LeftTerm a r x) ∧
      Summable (chapter6Entry16MiddleTerm a r x) ∧
      Summable (chapter6Entry16RightTerm a r x) ∧
      (∑' j : ℕ, chapter6Entry16LeftTerm a r x j) =
        (∑' j : ℕ, chapter6Entry16MiddleTerm a r x j) +
          ∑' j : ℕ, chapter6Entry16RightTerm a r x j := by
  have hRne : ∀ k : ℕ, 1 ≤ k → 1 - r * x ^ (k - 1) ≠ 0 :=
    fun k hk => rightDenom_ne hr hx k hk
  have hrow : ∀ m, ∑' n, triFun a r x n m
      = chapter6Entry16LeftTerm a r x m - chapter6Entry16MiddleTerm a r x m :=
    fun m => row_tsum hpoles m
  have hcol : ∀ n, ∑' m, triFun a r x n m
      = chapter6Entry16RightTerm a r x n :=
    fun n => column_tsum hr hx n
  by_cases hξ1 : ‖x‖ = 1
  · obtain ⟨δ, hδ0, hδ⟩ := hboundarySeparated hξ1
    have har : ‖a * r‖ < 1 := hboundary hξ1
    have har' : ‖a‖ * ‖r‖ < 1 := by rwa [norm_mul] at har
    have hL := summable_left_of_denom_bound hr hδ0 hδ
    have hM := summable_middle_of_boundary har' hξ1 hδ0 hδ
    have hR := summable_right_of_boundary hr har' hξ1
    have hgB : Summable (triBound a r x) := by
      have heq : triBound a r x
          = fun n => (‖r‖ / (1 - ‖r‖)) * (‖a‖ * ‖r‖) ^ n := by
        funext n
        unfold triBound
        rw [hξ1, one_pow, mul_one]
      rw [heq]
      exact (summable_real_geometric
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) har').mul_left _
    have hpair : Summable (Function.uncurry (triFun a r x)) :=
      summable_uncurry_of_fiber_bounds (fun n => triBound_nonneg _ _ _ hr n)
        (fun n => fiber_norm_summable hr hx n)
        (fun n => column_le_bound hr hx n)
        hgB
    have heq := fubini_step hL hM hR hpair hrow hcol
    exact ⟨hRne, hL, hM, hR, heq⟩
  · have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hx (fun h => hξ1 h)
    have hev := eventually_norm_ax_le_half (a := a) hxlt
    have hL := summable_left_of_interior hr hev
    have hM := summable_middle_of_interior hr hev
    have hR := summable_right_of_interior hr hx hev
    have h1ρ : (0 : ℝ) < 1 - ‖r‖ := sub_pos.mpr hr
    have hC : (0 : ℝ) ≤ ‖r‖ / (1 - ‖r‖) :=
      div_nonneg (norm_nonneg _) h1ρ.le
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hgI : Summable (triBound a r x) := by
      apply Summable.of_norm_bounded_eventually
        (g := fun n : ℕ => (‖r‖ / (1 - ‖r‖)) * (1 / 2 : ℝ) ^ n)
      · exact (summable_real_geometric (by norm_num) (by norm_num)).mul_left _
      · have h2 : ∀ᶠ n : ℕ in Filter.atTop,
            ‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1) ≤ 1 / 2 :=
          Filter.eventually_atTop.mpr ⟨N, fun n _ => by
            have hjt := hN (n + 1) (by omega)
            have e : ‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1) = ‖r‖ * ‖a * x ^ (n + 1)‖ := by
              rw [norm_mul, norm_pow]
              ring
            rw [e]
            calc ‖r‖ * ‖a * x ^ (n + 1)‖ ≤ 1 * (1 / 2) :=
                  mul_le_mul (le_of_lt hr) hjt (norm_nonneg _) (by norm_num)
            _ = 1 / 2 := one_mul _⟩
        have h1 := eventually_cofinite_of_atTop h2
        filter_upwards [h1] with n hn
        rw [Real.norm_eq_abs, abs_of_nonneg (triBound_nonneg _ _ _ hr n)]
        unfold triBound
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hn _) hC
    have hpair : Summable (Function.uncurry (triFun a r x)) :=
      summable_uncurry_of_fiber_bounds (fun n => triBound_nonneg _ _ _ hr n)
        (fun n => fiber_norm_summable hr hx n)
        (fun n => column_le_bound hr hx n)
        hgI
    have heq := fubini_step hL hM hR hpair hrow hcol
    exact ⟨hRne, hL, hM, hR, heq⟩

end

end Entry16InfiniteSum

end MathlibExt.Analysis.Ramanujan.Part1Ch6
