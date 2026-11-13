/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CriticalPoint
import Code.Onsager.FreeEnergy
import Code.Onsager.RiemannPeriodic2D
import Code.Onsager.SymbolDet

open scoped Real
open MeasureTheory

namespace StatMech.Onsager



theorem ons_gInt_pos_of_ne_betaC (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (k₁ k₂ : ℝ) : 0 < ons_gInt β k₁ k₂ := by
  have hsinh : Real.sinh (2 * β) ≠ 1 := by
    intro hs
    by_cases hβ0 : β = 0
    · subst β
      norm_num at hs
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      exact hcrit ((ons_betaC_unique β hβpos).mp hs)
  have hzero : 0 < ons_gInt β 0 0 := by
    rw [ons_gInt_zero]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hsinh)
  exact lt_of_lt_of_le hzero (ons_gInt_min β k₁ k₂ hβ)


theorem continuous_log_ons_gInt (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC) :
    Continuous (fun p : ℝ × ℝ => Real.log (ons_gInt β p.1 p.2)) := by
  apply Continuous.log
  · unfold ons_gInt
    fun_prop
  · intro p
    exact ne_of_gt (ons_gInt_pos_of_ne_betaC β hβ hcrit p.1 p.2)


theorem periodic_log_ons_gInt_left (β k₂ : ℝ) :
    Function.Periodic (fun k₁ => Real.log (ons_gInt β k₁ k₂)) (2 * Real.pi) := by
  intro k₁
  simp only [ons_gInt, Real.cos_add_two_pi]


theorem periodic_log_ons_gInt_right (β k₁ : ℝ) :
    Function.Periodic (fun k₂ => Real.log (ons_gInt β k₁ k₂)) (2 * Real.pi) := by
  intro k₂
  simp only [ons_gInt, Real.cos_add_two_pi]



theorem integral_log_ons_gInt_right_shift (β k₁ : ℝ) :
    (∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
      ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂) := by
  have h := (periodic_log_ons_gInt_right β k₁).intervalIntegral_add_eq 0 (-Real.pi)
  convert h using 1 <;> ring


theorem integral_log_ons_gInt_square_shift (β : ℝ) :
    (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
      ∫ k₁ in (-Real.pi)..Real.pi,
        ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂) := by
  let g : ℝ → ℝ := fun k₁ =>
    ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂)
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro k₁
    apply intervalIntegral.integral_congr
    intro k₂ _
    exact congrArg Real.log (by
      simp only [ons_gInt, Real.cos_add_two_pi])
  calc
    (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
        ∫ k₁ in (0 : ℝ)..(2 * Real.pi), g k₁ := by
          apply intervalIntegral.integral_congr
          intro k₁ _
          exact integral_log_ons_gInt_right_shift β k₁
    _ = ∫ k₁ in (-Real.pi)..Real.pi, g k₁ := by
      have h := hgper.intervalIntegral_add_eq 0 (-Real.pi)
      convert h using 1 <;> ring
    _ = _ := rfl


theorem ons_log_gInt_riemann_tendsto (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC) :
    Filter.Tendsto
      (fun n : ℕ => (2 * Real.pi / n) ^ 2 *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_gInt β (2 * Real.pi * i / n) (2 * Real.pi * j / n)))
      Filter.atTop
      (nhds (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂))) := by
  exact ons_riemann_periodic_two
    (fun k₁ k₂ => Real.log (ons_gInt β k₁ k₂))
    (continuous_log_ons_gInt β hβ hcrit)
    (fun k₂ => periodic_log_ons_gInt_left β k₂)



theorem ons_log_gInt_density_tendsto (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_gInt β (2 * Real.pi * i / n) (2 * Real.pi * j / n)))
      Filter.atTop (nhds (ons_freeEnergyIntegral β)) := by
  let c : ℝ := 1 / (8 * Real.pi ^ 2)
  have hscaled := (ons_log_gInt_riemann_tendsto β hβ hcrit).const_mul c
  have hlim : c *
      (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
      ons_freeEnergyIntegral β := by
    rw [integral_log_ons_gInt_square_shift]
    rfl
  rw [hlim] at hscaled
  refine hscaled.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [c]
  field_simp [hn0, Real.pi_ne_zero]
  ring


noncomputable def ons_symbolDispersion (β k₁ k₂ : ℝ) : ℝ :=
  (1 + Real.tanh β ^ 2) ^ 2 -
    2 * Real.tanh β * (1 - Real.tanh β ^ 2) * (Real.cos k₁ + Real.cos k₂)

theorem ons_symbolDispersion_eq (β k₁ k₂ : ℝ) :
    ons_symbolDispersion β k₁ k₂ = ons_gInt β k₁ k₂ / Real.cosh β ^ 4 := by
  exact ons_dispersion_cosh β (Real.cos k₁ + Real.cos k₂)

theorem ons_symbolDispersion_pos (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (k₁ k₂ : ℝ) : 0 < ons_symbolDispersion β k₁ k₂ := by
  rw [ons_symbolDispersion_eq]
  exact div_pos (ons_gInt_pos_of_ne_betaC β hβ hcrit k₁ k₂)
    (pow_pos (Real.cosh_pos β) 4)


theorem log_ons_symbolDispersion (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC)
    (k₁ k₂ : ℝ) :
    Real.log (ons_symbolDispersion β k₁ k₂) =
      Real.log (ons_gInt β k₁ k₂) - 4 * Real.log (Real.cosh β) := by
  rw [ons_symbolDispersion_eq, Real.log_div
    (ne_of_gt (ons_gInt_pos_of_ne_betaC β hβ hcrit k₁ k₂))
    (pow_ne_zero 4 (Real.cosh_pos β).ne'), Real.log_pow]
  norm_num


theorem ons_symbolDispersion_density_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_symbolDispersion β
            (2 * Real.pi * i / n) (2 * Real.pi * j / n)))
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have ht := (ons_log_gInt_density_tendsto β hβ hcrit).sub_const
    (2 * Real.log (Real.cosh β))
  refine ht.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp_rw [log_ons_symbolDispersion β hβ hcrit, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hn0]
  ring


theorem ons_log_gInt_density_shift_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_gInt β
            (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n)))
      Filter.atTop (nhds (ons_freeEnergyIntegral β)) := by
  have hR := ons_riemann_periodic_two_shift
    (fun k₁ k₂ => Real.log (ons_gInt β k₁ k₂))
    (continuous_log_ons_gInt β hβ hcrit)
    (fun k₂ => periodic_log_ons_gInt_left β k₂) s t hs ht
  let c : ℝ := 1 / (8 * Real.pi ^ 2)
  have hscaled := hR.const_mul c
  have hlim : c *
      (∫ k₁ in (0 : ℝ)..(2 * Real.pi),
        ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.log (ons_gInt β k₁ k₂)) =
      ons_freeEnergyIntegral β := by
    rw [integral_log_ons_gInt_square_shift]
    rfl
  rw [hlim] at hscaled
  refine hscaled.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [c]
  field_simp [hn0, Real.pi_ne_zero]
  ring


theorem ons_symbolDispersion_density_shift_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (hcrit : β ≠ ons_betaC) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (2 * (n : ℝ) ^ 2)) *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Real.log (ons_symbolDispersion β
            (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n)))
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have htend := (ons_log_gInt_density_shift_tendsto β hβ hcrit s t hs ht).sub_const
    (2 * Real.log (Real.cosh β))
  refine htend.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp_rw [log_ons_symbolDispersion β hβ hcrit, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hn0]
  ring

end StatMech.Onsager
