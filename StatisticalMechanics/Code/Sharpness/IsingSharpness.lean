/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Sharpness.MeanfieldIsing

open Finset Real





set_option linter.unusedVariables false

namespace StatMech

namespace Sharpness

namespace IsingSharp













theorem susceptibility_fixed_point {S φ χ : ℝ} (hφ1 : φ < 1)
    (hself : χ ≤ S + φ * χ) :
    χ ≤ S / (1 - φ) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - φ)]
  nlinarith













theorem finite_susceptibility {V : Type*} (origin : V) (corr : V → V → ℝ)
    (hcorr_nonneg : ∀ x z, 0 ≤ corr x z)
    (cardS : ℕ) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    
    (hsimon : ∀ Λ : Finset V,
      (∑ z ∈ Λ, corr origin z) ≤ (cardS : ℝ) + φ * ((cardS : ℝ) / (1 - φ))) :
    Summable (corr origin) ∧ (∑' x, corr origin x) ≤ (cardS : ℝ) / (1 - φ) := by
  have hden : (0 : ℝ) < 1 - φ := by linarith
  
  have hbound : ∀ Λ : Finset V, (∑ z ∈ Λ, corr origin z) ≤ (cardS : ℝ) / (1 - φ) := by
    intro Λ
    refine le_trans (hsimon Λ) ?_
    
    have : (cardS : ℝ) + φ * ((cardS : ℝ) / (1 - φ)) = (cardS : ℝ) / (1 - φ) := by
      field_simp; ring
    rw [this]
  have hsum : Summable (corr origin) :=
    summable_of_sum_le (fun z => hcorr_nonneg origin z) hbound
  refine ⟨hsum, ?_⟩
  exact hsum.tsum_le_of_sum_le hbound














theorem geometric_decay (L : ℕ) (hL : 1 ≤ L) (φ : ℝ) (hφ0 : 0 ≤ φ)
    (f : ℕ → ℝ) (hf0 : ∀ r, 0 ≤ f r) (hf1 : ∀ r, f r ≤ 1)
    (hstep : ∀ r, L < r → f r ≤ φ * f (r - L)) :
    ∀ r, f r ≤ φ ^ ((r - 1) / L) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases hr : L < r
    · have hrec := hstep r hr
      have hlt : r - L < r := by omega
      have ih' := ih (r - L) hlt
      have harith : (r - 1) / L = ((r - L) - 1) / L + 1 := by
        have h1 : r - 1 = (r - L - 1) + L := by omega
        rw [h1, Nat.add_div_right _ (by omega : 0 < L)]
      calc f r ≤ φ * f (r - L) := hrec
        _ ≤ φ * φ ^ ((r - L - 1) / L) := mul_le_mul_of_nonneg_left ih' hφ0
        _ = φ ^ ((r - L - 1) / L + 1) := by rw [pow_succ]; ring
        _ = φ ^ ((r - 1) / L) := by rw [harith]
    · rw [not_lt] at hr
      have hz : (r - 1) / L = 0 := Nat.div_eq_of_lt (by omega)
      rw [hz, pow_zero]; exact hf1 r






theorem geometric_le_exp (L : ℕ) (hL : 1 ≤ L) (φ : ℝ) (hpos : 0 < φ)
    (hφ1 : φ < 1) (r : ℕ) :
    φ ^ ((r - 1) / L) ≤ (1 / φ) * Real.exp ((Real.log φ / L) * r) := by
  have hL0 : (0 : ℕ) < L := hL
  have hlogneg : Real.log φ < 0 := Real.log_neg hpos hφ1
  set k : ℕ := (r - 1) / L with hk
  have hnat : (r : ℝ) ≤ L * (k : ℝ) + L := by
    have h1 := Nat.div_add_mod (r - 1) L
    have h2 := Nat.mod_lt (r - 1) hL0
    have hr : r ≤ L * k + L := by rw [hk]; omega
    have hcast : (r : ℝ) ≤ ((L * k + L : ℕ) : ℝ) := by exact_mod_cast hr
    push_cast at hcast; linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
  rw [show φ ^ k = Real.exp ((k : ℝ) * Real.log φ) by
        rw [mul_comm, Real.exp_mul, Real.exp_log hpos, ← Real.rpow_natCast]]
  rw [one_div, ← Real.exp_log (show (0 : ℝ) < φ⁻¹ by positivity)]
  rw [← Real.exp_add, Real.log_inv]
  apply Real.exp_le_exp.mpr
  have hfac : -Real.log φ + Real.log φ / L * r - (k : ℝ) * Real.log φ
      = Real.log φ * ((r : ℝ) / L - (k + 1)) := by field_simp; ring
  have hpos2 : 0 ≤ Real.log φ * ((r : ℝ) / L - (k + 1)) :=
    mul_nonneg_of_nonpos_of_nonpos hlogneg.le
      (by rw [sub_nonpos, div_le_iff₀ hLpos]; linarith [hnat])
  linarith [hfac ▸ hpos2]










theorem exponential_decay (L : ℕ) (hL : 1 ≤ L) (φ : ℝ) (hpos : 0 < φ)
    (hφ1 : φ < 1) (f : ℕ → ℝ) (hf0 : ∀ r, 0 ≤ f r) (hf1 : ∀ r, f r ≤ 1)
    (hstep : ∀ r, L < r → f r ≤ φ * f (r - L)) :
    ∃ c > 0, ∃ C > 0, ∀ r : ℕ, f r ≤ C * Real.exp (-c * r) := by
  refine ⟨- (Real.log φ / L), ?_, 1 / φ, by positivity, ?_⟩
  · 
    have hlogneg : Real.log φ < 0 := Real.log_neg hpos hφ1
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show (0 : ℕ) < L from hL)
    have : Real.log φ / L < 0 := div_neg_of_neg_of_pos hlogneg hLpos
    linarith
  · intro r
    have hgeo := geometric_decay L hL φ hpos.le f hf0 hf1 hstep r
    have hbridge := geometric_le_exp L hL φ hpos hφ1 r
    calc f r ≤ φ ^ ((r - 1) / L) := hgeo
      _ ≤ (1 / φ) * Real.exp ((Real.log φ / L) * r) := hbridge
      _ = (1 / φ) * Real.exp (-(-(Real.log φ / L)) * r) := by rw [neg_neg]













theorem meanfield_bound (β₀ : ℝ) (hβ₀ : 0 < β₀) (m : ℝ → ℝ)
    (hdiff : ∀ β ∈ Set.Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
    (hineq : ∀ β ∈ Set.Ioi β₀, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
    (hzero : m β₀ = 0) (hnonneg : ∀ β ∈ Set.Ici β₀, 0 ≤ m β)
    {β : ℝ} (hβ : β₀ ≤ β) :
    Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β :=
  StatMech.Sharpness.meanfield_lower_bound β₀ hβ₀ m hdiff hineq hzero hnonneg hβ






























theorem ising_sharpness {V : Type*} (origin : V) (β_c : ℝ) (hβc : 0 < β_c)
    (m : ℝ → ℝ) (corr : V → V → ℝ)
    
    (hdiff : ∀ β ∈ Set.Ici β_c, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
    (hineq : ∀ β ∈ Set.Ioi β_c, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
    (hzero : m β_c = 0) (hmnonneg : ∀ β ∈ Set.Ici β_c, 0 ≤ m β)
    
    (hcorr_nonneg : ∀ x z, 0 ≤ corr x z)
    (cardS : ℕ) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hsimon : ∀ Λ : Finset V,
      (∑ z ∈ Λ, corr origin z) ≤ (cardS : ℝ) + φ * ((cardS : ℝ) / (1 - φ))) :
    
    (∀ β, β_c < β → Real.sqrt (1 - (β_c / β) ^ 2) ≤ m β) ∧
    
    (Summable (corr origin) ∧ (∑' x, corr origin x) ≤ (cardS : ℝ) / (1 - φ)) := by
  refine ⟨?_, ?_⟩
  · intro β hβ
    exact meanfield_bound β_c hβc m hdiff hineq hzero hmnonneg hβ.le
  · exact finite_susceptibility origin corr hcorr_nonneg cardS φ hφ0 hφ1 hsimon

end IsingSharp

end Sharpness

end StatMech
