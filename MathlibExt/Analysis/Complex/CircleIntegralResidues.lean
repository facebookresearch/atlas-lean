/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean`
and
`P2M/Sol/S_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.NhdsWithin

@[expose] public section

open Metric Filter
open scoped Topology

namespace Complex

/-- Circle integral of a function with finitely many simple poles in a disc.

If `h` is analytic at every point of the closed disc of radius `R` around
`z₀` outside a finite set `Z` lying strictly inside the disc, and near each
`a ∈ Z` it has the form `h z = c a / (z - a) + g z` with `g` analytic at
`a`, then the circle integral of `h` is `2πi` times the sum of the
residues `c a`. -/
public theorem circleIntegral_eq_sum_residue_of_simplePole
    {R : ℝ} {z₀ : ℂ} (hR : 0 < R) (h c : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a := by
  classical
  choose g hg hgeq using hloc
  have hZclosed : IsClosed ((Z : Set ℂ)) := Z.finite_toSet.isClosed
  have hsum_an : ∀ (S : Finset ℂ) (z : ℂ), (∀ b ∈ S, b ≠ z) →
      AnalyticAt ℂ (fun w => ∑ b ∈ S, c b * (w - b)⁻¹) z := by
    intro S z hne
    have h₁ : AnalyticAt ℂ (∑ b ∈ S, fun w => c b * (w - b)⁻¹) z :=
      Finset.analyticAt_sum S fun b hb =>
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.mpr (Ne.symm (hne b hb))))
    have heq : (∑ b ∈ S, fun w => c b * (w - b)⁻¹)
        = fun w => ∑ b ∈ S, c b * (w - b)⁻¹ := by
      funext w; simp
    exact heq ▸ h₁
  have hΦan : ∀ z ∈ Metric.closedBall z₀ R, AnalyticAt ℂ
      (fun w => if hw : w ∈ Z then g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
                else h w - ∑ b ∈ Z, c b * (w - b)⁻¹) z := by
    intro z hz
    by_cases hzZ : z ∈ Z
    · have hevNotZ : ∀ᶠ w in 𝓝[≠] z, w ∉ Z := by
        have hcl : IsClosed ((Z.erase z : Finset ℂ) : Set ℂ) :=
          (Z.erase z).finite_toSet.isClosed
        have hmem : z ∈ (((Z.erase z : Finset ℂ) : Set ℂ))ᶜ := by simp
        have h₁ : ∀ᶠ w in 𝓝 z, w ∈ (((Z.erase z : Finset ℂ) : Set ℂ))ᶜ :=
          hcl.isOpen_compl.eventually_mem hmem
        have h₂ : ∀ᶠ w in 𝓝[≠] z, w ∈ ({z}ᶜ : Set ℂ) :=
          eventually_mem_nhdsWithin
        filter_upwards [h₁.filter_mono nhdsWithin_le_nhds, h₂] with w hw₁ hw₂ hwZ
        simp only [Set.mem_compl_iff, Finset.coe_erase, Set.mem_diff,
          Set.mem_singleton_iff, Finset.mem_coe, not_and, not_not] at hw₁
        exact hw₂ (hw₁ hwZ)
      have hev : (fun w => if hw : w ∈ Z then
            g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝[≠] z] fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹ := by
        filter_upwards [hgeq z hzZ, hevNotZ] with w hw hwZ
        simp only [dite_eq_right hwZ]
        rw [hw, ← Finset.add_sum_erase Z _ hzZ]
        simp only [div_eq_mul_inv]
        ring
      have hΨan : AnalyticAt ℂ
          (fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹) z :=
        (hg z hzZ).sub (hsum_an _ z fun b hb => (Finset.mem_erase.mp hb).1)
      have hfull : (fun w => if hw : w ∈ Z then
            g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝 z] fun w => g z hzZ w - ∑ b ∈ Z.erase z, c b * (w - b)⁻¹ :=
        eventuallyEq_nhds_of_eventuallyEq_nhdsNE hev (by simp only [dite_eq_left hzZ])
      exact hΨan.congr hfull.symm
    · have hopen : ∀ᶠ w in 𝓝 z, w ∉ Z := by
        have : ∀ᶠ w in 𝓝 z, w ∈ ((Z : Set ℂ))ᶜ :=
          hZclosed.isOpen_compl.eventually_mem (by simpa using hzZ)
        simpa using this
      have hev : (fun w => if hw : w ∈ Z then
            g w hw w - ∑ b ∈ Z.erase w, c b * (w - b)⁻¹
            else h w - ∑ b ∈ Z, c b * (w - b)⁻¹)
          =ᶠ[𝓝 z] fun w => h w - ∑ b ∈ Z, c b * (w - b)⁻¹ := by
        filter_upwards [hopen] with w hw
        simp only [dite_eq_right hw]
      have han : AnalyticAt ℂ (fun w => h w - ∑ b ∈ Z, c b * (w - b)⁻¹) z :=
        (hh z hz hzZ).sub (hsum_an Z z fun b hb hbz => hzZ (hbz ▸ hb))
      exact han.congr hev.symm
  have h0 : (∮ z in C(z₀, R),
      (if hz : z ∈ Z then g z hz z - ∑ b ∈ Z.erase z, c b * (z - b)⁻¹
       else h z - ∑ b ∈ Z, c b * (z - b)⁻¹)) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty
      (fun z hz => ((hΦan z hz).continuousAt).continuousWithinAt)
      (fun z hz => (hΦan z (Metric.ball_subset_closedBall hz.1)).differentiableAt)
  have hZsphere : ∀ z ∈ Metric.sphere z₀ R, z ∉ Z := by
    intro z hzs hzZ
    have h₁ := hZ z hzZ
    rw [Metric.mem_ball] at h₁
    rw [Metric.mem_sphere] at hzs
    exact absurd hzs (ne_of_lt h₁)
  have h1 : (∮ z in C(z₀, R), (h z - ∑ b ∈ Z, c b * (z - b)⁻¹)) = 0 := by
    rw [circleIntegral.integral_congr (R := R) (c := z₀)
      (f := fun z => h z - ∑ b ∈ Z, c b * (z - b)⁻¹)
      (g := fun z => if hz : z ∈ Z then
        g z hz z - ∑ b ∈ Z.erase z, c b * (z - b)⁻¹
        else h z - ∑ b ∈ Z, c b * (z - b)⁻¹)
      hR.le (fun z hzs => by simp only [dite_eq_right (hZsphere z hzs)])]
    exact h0
  have hIntTerm : ∀ b ∈ Z, CircleIntegrable (fun z => c b * (z - b)⁻¹) z₀ R := by
    intro b hb
    have hbs : b ∉ Metric.sphere z₀ |R| := by
      intro hmem
      have h₁ := hZ b hb
      rw [Metric.mem_ball] at h₁
      rw [Metric.mem_sphere, abs_of_pos hR] at hmem
      exact absurd hmem (ne_of_lt h₁)
    have h₁ : CircleIntegrable (fun z => (z - b)⁻¹) z₀ R :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr hbs)
    have heq : (c b • fun z : ℂ => (z - b)⁻¹) = fun z => c b * (z - b)⁻¹ := by
      funext w; simp [smul_eq_mul]
    exact heq ▸ h₁.const_smul
  have hInth : CircleIntegrable h z₀ R :=
    ContinuousOn.circleIntegrable hR.le fun z hzs =>
      ((hh z (Metric.sphere_subset_closedBall hzs)
        (hZsphere z hzs)).continuousAt).continuousWithinAt
  have hIntP : CircleIntegrable (fun z => ∑ b ∈ Z, c b * (z - b)⁻¹) z₀ R := by
    have h₁ := CircleIntegrable.sum Z hIntTerm
    have heq : (∑ b ∈ Z, fun z => c b * (z - b)⁻¹)
        = fun z => ∑ b ∈ Z, c b * (z - b)⁻¹ := by
      funext w; simp
    exact heq ▸ h₁
  have h2 : (∮ z in C(z₀, R), h z)
      = ∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹ := by
    have h₁ : (∮ z in C(z₀, R), h z)
        - (∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹) = 0 := by
      rw [← circleIntegral.integral_sub hInth hIntP]
      exact h1
    exact sub_eq_zero.mp h₁
  have hterm : ∀ b ∈ Z, (∮ z in C(z₀, R), c b * (z - b)⁻¹)
      = c b * (2 * Real.pi * Complex.I) := by
    intro b hb
    have h₁ := circleIntegral.integral_smul (c b) (fun z => (z - b)⁻¹) z₀ R
    simp only [smul_eq_mul] at h₁
    rw [h₁, circleIntegral.integral_sub_inv_of_mem_ball (hZ b hb)]
  have h3 : (∮ z in C(z₀, R), ∑ b ∈ Z, c b * (z - b)⁻¹)
      = ∑ b ∈ Z, c b * (2 * Real.pi * Complex.I) := by
    rw [circleIntegral.integral_fun_sum hIntTerm]
    exact Finset.sum_congr rfl hterm
  rw [h2, h3, ← Finset.sum_mul]
  ring

end Complex
