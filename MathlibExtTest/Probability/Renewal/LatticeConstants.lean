/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.LatticeConstants

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tests for renewal lattice constants

Lattice non-vacuity witness: the geometric-type tail `F t = e^{-⌈t⌉}` on the
lattice `ℤ` (span `h = 1`, Cramér root `θ = 1`) has lattice constant `C = 1`;
the scaled tail oscillates with `limsup = 1`, `liminf = e^{-1}` and no limit.
Lattice-support bridge: a point mass at `2` sees `[1/2, ∞)` and `[1, ∞)` alike.
Exponential witness: the defective law `G(dy) = e^{-2y} dy` on `(0, ∞)` (mass
`½`) has Cramér root `θ = 1`, tilted law `Exp(1)` with mean `1`, exact strict
tail `Z t = ½ e^{-t}` solving the renewal equation, an admissible tilted pair,
and Cramér–Lundberg constant `½`, matching `e^{t} Z t = ½`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace MathlibExtTest.Probability.Renewal.LatticeConstants

open MathlibExt.Probability.Renewal.LatticeConstants

/-! ### Lattice witness `F t = e^{-⌈t⌉}`, `h = 1`, `θ = 1` -/

private lemma step : ∀ t : ℝ, exp (-(⌈t⌉ : ℝ)) = exp (-(⌈(1 : ℝ) * ⌈t / 1⌉⌉ : ℝ)) := by
  intro t
  simp

private lemma lat : Tendsto (fun k : ℕ => exp (1 * (k * 1)) * exp (-(⌈(k : ℝ) * 1⌉ : ℝ)))
    atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr fun k => ?_
  simp only [mul_one, one_mul]
  rw [Int.ceil_natCast, ← exp_add]
  push_cast
  simp

-- Offset `s = 1/2`: the scaled tail tends to `e^{-1/2}` there.
example : Tendsto (fun k : ℕ => exp (1 * (k * 1 - 1 / 2)) * exp (-(⌈(k : ℝ) * 1 - 1 / 2⌉ : ℝ)))
    atTop (𝓝 (exp (-(1 * (1 / 2))) * 1)) :=
  tendsto_scaled_tail_offset (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos step lat
    (by norm_num) (by norm_num)

-- Upper envelope: `limsup = C = 1`.
example : limsup (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop = 1 :=
  limsup_scaled_tail_eq (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos zero_le_one
    (fun _ => (exp_pos _).le) step lat

-- Lower envelope: `liminf = e^{-θ h} C = e^{-1}`.
example : liminf (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop = exp (-(1 * 1)) * 1 :=
  liminf_scaled_tail_eq (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos zero_le_one
    (fun _ => (exp_pos _).le) step lat

-- Dichotomy: no limit over the reals, for any candidate constant.
example (L : ℝ) : ¬ Tendsto (fun t : ℝ => exp (1 * t) * exp (-(⌈t⌉ : ℝ))) atTop (𝓝 L) :=
  not_tendsto_scaled_tail (F := fun t => exp (-(⌈t⌉ : ℝ))) one_pos one_pos one_ne_zero step lat L

/-! ### Lattice-support bridge -/

private lemma ceil_half : ⌈(1 : ℝ) / 2 / 1⌉ = 1 := by
  rw [Int.ceil_eq_iff]
  norm_num

-- A point mass at `0` on the lattice `ℤ`: `[1/2, ∞)` and `[1, ∞)` both miss it.
-- (Rounding down instead would compare with `[0, ∞)`, which has mass `1`.)
example : Measure.dirac (0 : ℝ) (Ici ((1 : ℝ) / 2)) = Measure.dirac (0 : ℝ) (Ici 1) := by
  rw [measure_Ici_eq_measure_Ici_ceil one_pos (by rw [ae_dirac_eq]; exact ⟨0, by norm_num⟩),
    ceil_half]
  norm_num

-- Strict versus weak tails: `δ₀ (0, ∞) = δ₀ [1, ∞) = 0`. (Confusing the strict tail
-- with the weak one at the same point would compare with `δ₀ [0, ∞) = 1`.)
example : Measure.dirac (0 : ℝ) (Ioi ((0 : ℤ) * 1)) = Measure.dirac (0 : ℝ) (Ici 1) := by
  rw [measure_Ioi_eq_measure_Ici_add one_pos (by rw [ae_dirac_eq]; exact ⟨0, by norm_num⟩)]
  norm_num

/-! ### Exponential witness: `G = ½ · Exp(2)`, Cramér root `θ = 1`

`G(dy) = e^{-2 y} dy` on `(0, ∞)` has mass `½`; `∫ e^{y} dG = 1`, so `θ = 1`, the
tilted law is `Exp(1)` (mean `1`), and the Cramér–Lundberg constant is
`(1 - ½) / (1 · 1) = ½`. The maximum of the ladder process has the exact strict
tail `Z t = ½ e^{-t}` for `t ≥ 0`, which solves the renewal equation. -/

/-- The defective exponential ladder law `e^{-2 y} dy` on `(0, ∞)`. -/
private noncomputable def Gex : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun y => ENNReal.ofReal (exp (-2 * y)))

/-- The exact strict tail `Z t = 1_{t ≥ 0} ½ e^{-t}`. -/
private noncomputable def Zex : ℝ → ℝ := (Ici 0).indicator (fun t => exp (-t) / 2)

private lemma integral_Gex (f : ℝ → ℝ) :
    ∫ y, f y ∂Gex = ∫ y in Ioi 0, exp (-2 * y) * f y := by
  rw [Gex, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]

private instance : IsFiniteMeasure Gex := by
  rw [Gex]
  exact isFiniteMeasure_withDensity_ofReal (integrableOn_exp_mul_Ioi (by norm_num) 0).2

private lemma Gex_root : ∫ y, exp (1 * y) ∂Gex = 1 := by
  rw [integral_Gex]
  have : ∀ y : ℝ, exp (-2 * y) * exp (1 * y) = exp (-1 * y) := fun y => by
    rw [← exp_add]; ring_nf
  simp_rw [this]
  rw [integral_exp_mul_Ioi (by norm_num)]
  norm_num

private lemma Gex_nonneg : ∀ᵐ y ∂Gex, 0 ≤ y := by
  rw [Gex]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_mem measurableSet_Ioi).mono fun y hy => le_of_lt hy)

private lemma Gex_mean : ∫ y, y * exp (1 * y) ∂Gex = 1 := by
  rw [integral_Gex]
  have : ∀ y : ℝ, exp (-2 * y) * (y * exp (1 * y)) = exp (-y) * y ^ ((2 : ℝ) - 1) := fun y => by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, mul_left_comm, ← exp_add]; ring_nf
  simp_rw [this]
  rw [← Real.Gamma_eq_integral two_pos, Real.Gamma_two]

private lemma Gex_meanIntegrable : Integrable (fun y => y * exp (1 * y)) Gex :=
  Integrable.of_integral_ne_zero (by rw [Gex_mean]; exact one_ne_zero)

private lemma Gex_univ : Gex.real univ = 1 / 2 := by
  have := integral_const (μ := Gex) (1 : ℝ)
  rw [smul_eq_mul, mul_one, integral_Gex] at this
  rw [← this]
  simp_rw [mul_one]
  rw [integral_exp_mul_Ioi (by norm_num)]
  norm_num

private lemma Gex_tail {t : ℝ} (ht : 0 ≤ t) : Gex.real (Ioi t) = exp (-2 * t) / 2 := by
  rw [← integral_indicator_one measurableSet_Ioi, integral_Gex]
  have : ∀ y, exp (-2 * y) * (Ioi t).indicator 1 y = (Ioi t).indicator (fun y => exp (-2 * y)) y :=
    fun y => by by_cases hy : y ∈ Ioi t <;> simp [hy]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 ht,
    integral_exp_mul_Ioi (by norm_num)]
  ring

private lemma Zex_renewal :
    ∀ t, Zex t = (Ici 0).indicator (fun s => Gex.real (Ioi s)) t + ∫ y, Zex (t - y) ∂Gex := by
  intro t
  rw [integral_Gex]
  rcases lt_or_ge t 0 with ht | ht
  · have hnot : t ∉ Ici (0 : ℝ) := fun h => absurd (mem_Ici.1 h) (not_le.2 ht)
    have hz : ∀ y ∈ Ioi (0 : ℝ), exp (-2 * y) * Zex (t - y) = 0 := fun y hy => by
      have : t - y ∉ Ici (0 : ℝ) := fun h => by
        have := mem_Ici.1 h; have := mem_Ioi.1 hy; linarith
      simp [Zex, indicator_of_notMem this]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero]
    simp [Zex, indicator_of_notMem hnot]
  · have hcut : ∀ y, exp (-2 * y) * Zex (t - y) =
        (Iic t).indicator (fun y => exp (-t) / 2 * exp (-1 * y)) y := fun y => by
      by_cases hy : y ∈ Iic t
      · have : t - y ∈ Ici (0 : ℝ) := mem_Ici.2 (by have := mem_Iic.1 hy; linarith)
        rw [indicator_of_mem hy, Zex, indicator_of_mem this, mul_div_assoc', ← exp_add]
        rw [div_mul_eq_mul_div, ← exp_add]
        congr 2
        ring
      · have : t - y ∉ Ici (0 : ℝ) := fun h => hy (mem_Iic.2 (by have := mem_Ici.1 h; linarith))
        rw [indicator_of_notMem hy, Zex, indicator_of_notMem this, mul_zero]
    simp_rw [hcut]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, integral_const_mul,
      ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_mul_left (fun y => exp y) (by norm_num : (-1 : ℝ) ≠ 0),
      integral_exp, Zex, indicator_of_mem (mem_Ici.2 ht), indicator_of_mem (mem_Ici.2 ht),
      Gex_tail ht]
    have : exp (-2 * t) = exp (-t) * exp (-t) := by rw [← exp_add]; ring_nf
    rw [this]
    simp only [mul_zero, exp_zero, smul_eq_mul, neg_mul, one_mul]
    ring

private lemma Zex_measurable : Measurable Zex :=
  (by fun_prop : Measurable fun t : ℝ => exp (-t) / 2).indicator measurableSet_Ici

private lemma Zex_neg : ∀ t < 0, Zex t = 0 := fun _ ht =>
  indicator_of_notMem (fun h => absurd (mem_Ici.1 h) (not_le.2 ht)) _

private lemma Zex_bdd : ∃ M, ∀ t, |Zex t| ≤ M := by
  refine ⟨1, fun t => ?_⟩
  by_cases ht : t ∈ Ici (0 : ℝ)
  · rw [Zex, indicator_of_mem ht, abs_of_pos (by positivity)]
    have : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith [mem_Ici.1 ht])
    linarith
  · rw [Zex, indicator_of_notMem ht, abs_zero]
    exact zero_le_one

-- The tilted law is a probability measure with mean `1`.
example : IsProbabilityMeasure (Gex.tilted (fun y => 1 * y)) :=
  isProbabilityMeasure_tilted_of_integral_eq_one Gex_root

example : ∫ y, y ∂(Gex.tilted (fun y => 1 * y)) = 1 := by
  rw [integral_id_tilt Gex_root, Gex_mean]

-- Tilting the renewal equation for the exact tail.
example (t : ℝ) : exp (1 * t) * Zex t =
    exp (1 * t) * (Ici 0).indicator (fun s => Gex.real (Ioi s)) t +
      ∫ y, exp (1 * (t - y)) * Zex (t - y) ∂(Gex.tilted (fun y => 1 * y)) :=
  tilted_renewal_eq Gex_root Zex_renewal t

-- Non-vacuity of the admissibility premise: the tilted Cramér–Lundberg pair of the
-- exponential example is `KeyRenewalAdmissible`.
example : KeyRenewalAdmissible (fun t => exp (1 * t) * Zex t)
    (fun t => exp (1 * t) * (Ici 0).indicator (fun s => Gex.real (Ioi s)) t) :=
  keyRenewalAdmissible_cramerLundberg one_pos Gex_root Gex_nonneg Gex_meanIntegrable
    Zex_measurable Zex_neg Zex_bdd

-- The Cramér–Lundberg constant of the example is `½`.
example : (1 - Gex.real univ) / (1 * ∫ y, y * exp (1 * y) ∂Gex) = 1 / 2 := by
  rw [Gex_univ, Gex_mean]
  norm_num

-- The conclusion of `tendsto_scaled_cramerLundberg` holds for the example, checked
-- directly from the exact tail (`e^{t} Z t = ½` for `t ≥ 0`), without `hKRT`.
example : Tendsto (fun t => exp (1 * t) * Zex t) atTop
    (𝓝 ((1 - Gex.real univ) / (1 * ∫ y, y * exp (1 * y) ∂Gex))) := by
  rw [Gex_univ, Gex_mean]
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)
  simp only [Zex]
  rw [indicator_of_mem (mem_Ici.2 ht), mul_div_assoc', ← exp_add]
  norm_num

end MathlibExtTest.Probability.Renewal.LatticeConstants
