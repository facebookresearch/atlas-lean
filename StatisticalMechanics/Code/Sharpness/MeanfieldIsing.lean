/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib

open MeasureTheory Real Set

namespace StatMech

namespace Sharpness















theorem meanfield_ode_antitone (β₀ : ℝ) (hβ₀ : 0 < β₀) (u : ℝ → ℝ)
    (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ u β)
    (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - u β) ≤ deriv u β) :
    AntitoneOn (fun β => β ^ 2 * (1 - u β)) (Ici β₀) := by
  set g : ℝ → ℝ := fun β => β ^ 2 * (1 - u β) with hg
  
  have hgderiv : ∀ β ∈ Ioi β₀, deriv g β = 2 * β * (1 - u β) - β ^ 2 * deriv u β := by
    intro β hβ
    have hβ0 : β ∈ Ici β₀ := le_of_lt (mem_Ioi.mp hβ)
    have hd := hdiff β hβ0
    have hH : HasDerivAt g (2 * β * (1 - u β) - β ^ 2 * deriv u β) β := by
      have h1 : HasDerivAt (fun β : ℝ => β ^ 2) (2 * β) β := by
        simpa using (hasDerivAt_pow 2 β)
      have h2 : HasDerivAt (fun β : ℝ => 1 - u β) (- deriv u β) β := by
        simpa using (hasDerivAt_const β (1 : ℝ)).sub hd.hasDerivAt
      have := h1.mul h2
      convert this using 1
      ring
    exact hH.deriv
  
  have hgnonpos : ∀ β ∈ Ioi β₀, deriv g β ≤ 0 := by
    intro β hβ
    have hβpos : 0 < β := lt_trans hβ₀ (mem_Ioi.mp hβ)
    rw [hgderiv β hβ]
    have key := hineq β hβ
    have hub : β ^ 2 * ((2 / β) * (1 - u β)) ≤ β ^ 2 * deriv u β :=
      mul_le_mul_of_nonneg_left key (by positivity)
    have hsimp : β ^ 2 * ((2 / β) * (1 - u β)) = 2 * β * (1 - u β) := by
      rw [show β ^ 2 * ((2 / β) * (1 - u β)) = (β ^ 2 / β) * 2 * (1 - u β) by ring,
          pow_two, mul_div_assoc, div_self hβpos.ne', mul_one]
      ring
    rw [hsimp] at hub
    linarith
  
  have hcont : ContinuousOn g (Ici β₀) := by
    apply ContinuousOn.mul
    · exact (continuous_pow 2).continuousOn
    · apply ContinuousOn.sub continuousOn_const
      intro β hβ
      exact (hdiff β hβ).continuousAt.continuousWithinAt
  have hdon : DifferentiableOn ℝ g (interior (Ici β₀)) := by
    rw [interior_Ici]
    intro β hβ
    have hβ0 : β ∈ Ici β₀ := le_of_lt (mem_Ioi.mp hβ)
    exact ((differentiableAt_pow 2).mul
      ((differentiableAt_const 1).sub (hdiff β hβ0))).differentiableWithinAt
  
  apply antitoneOn_of_deriv_nonpos (convex_Ici β₀) hcont hdon
  rw [interior_Ici]
  exact hgnonpos








theorem meanfield_one_minus_le (β₀ : ℝ) (hβ₀ : 0 < β₀) (u : ℝ → ℝ)
    (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ u β)
    (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - u β) ≤ deriv u β)
    {β : ℝ} (hβ : β₀ ≤ β) :
    1 - u β ≤ (β₀ / β) ^ 2 * (1 - u β₀) := by
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ
  have hanti := meanfield_ode_antitone β₀ hβ₀ u hdiff hineq
  have hmono : β ^ 2 * (1 - u β) ≤ β₀ ^ 2 * (1 - u β₀) :=
    hanti self_mem_Ici (mem_Ici.mpr hβ) hβ
  
  rw [div_pow, mul_comm_div, mul_div_assoc']
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
  calc (1 - u β) * β ^ 2 = β ^ 2 * (1 - u β) := by ring
    _ ≤ β₀ ^ 2 * (1 - u β₀) := hmono
    _ = β₀ ^ 2 * (1 - u β₀) := rfl













theorem meanfield_lower_bound (β₀ : ℝ) (hβ₀ : 0 < β₀) (m : ℝ → ℝ)
    (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
    (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
    (hzero : m β₀ = 0) (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
    {β : ℝ} (hβ : β₀ ≤ β) :
    Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀ hβ
  
  have hgw := meanfield_one_minus_le β₀ hβ₀ (fun β => (m β) ^ 2) hdiff hineq hβ
  simp only at hgw
  rw [hzero] at hgw
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    mul_one] at hgw
  
  have h2 : 1 - (β₀ / β) ^ 2 ≤ (m β) ^ 2 := by linarith
  calc Real.sqrt (1 - (β₀ / β) ^ 2)
      ≤ Real.sqrt ((m β) ^ 2) := Real.sqrt_le_sqrt h2
    _ = m β := Real.sqrt_sq (hnonneg β (mem_Ici.mpr hβ))

end Sharpness

end StatMech
