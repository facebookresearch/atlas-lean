/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ParticleBalances.SizeIndependentGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact fixtures at a nonzero lower endpoint, with and without transport and loss. -/

namespace Chemistry.ParticleBalances

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def profile (x : ℝ) : ℝ := Real.exp (2 - x)

private lemma profile_deriv (x : ℝ) : HasDerivAt profile (-profile x) x := by
  change HasDerivAt (fun y ↦ Real.exp (2 - y)) (-Real.exp (2 - x)) x
  simpa using (((hasDerivAt_id x).const_sub (2 : ℝ)).exp)

private lemma profile_tail (k : ℕ) : Tendsto (fun x ↦ x ^ k * profile x) atTop (𝓝 0) := by
  simpa only [profile, sub_eq_add_neg, Real.exp_add, mul_left_comm, mul_zero] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul (Real.exp 2)

private lemma profile_mass : IntegrableOn profile (Ioi 2) ∧ (∫ x in Ioi 2, profile x) = 1 := by
  have hd : ∀ x ∈ Ici (2 : ℝ), HasDerivAt (fun y ↦ -profile y) (profile x) x := fun x _ ↦ by
    have h := (profile_deriv x).neg
    change HasDerivAt (fun y ↦ -profile y) (- -profile x) x at h
    simpa only [neg_neg] using h
  have hp : ∀ x ∈ Ioi (2 : ℝ), 0 ≤ profile x := fun x _ ↦ (Real.exp_pos (2 - x)).le
  have hlim : Tendsto (fun x ↦ -profile x) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_zero] using (profile_tail 0).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hlim, ?_⟩
  simpa [profile] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hlim

private lemma profile_first : IntegrableOn (fun x ↦ x * profile x) (Ioi 2) ∧
    (∫ x in Ioi 2, x * profile x) = 3 := by
  have hd : ∀ x ∈ Ici (2 : ℝ), HasDerivAt (fun y ↦ -(y + 1) * profile y) (x * profile x) x := by
    intro x _
    have h := (((hasDerivAt_id x).add_const 1).neg.mul (profile_deriv x))
    change HasDerivAt (fun y ↦ -(y + 1) * profile y)
      (-1 * profile x + -(x + 1) * -profile x) x at h
    rwa [show -1 * profile x + -(x + 1) * -profile x = x * profile x by ring] at h
  have hp : ∀ x ∈ Ioi (2 : ℝ), 0 ≤ x * profile x := fun x hx ↦
    mul_nonneg (le_trans (by norm_num) (le_of_lt hx)) (Real.exp_pos (2 - x)).le
  have hlim : Tendsto (fun x ↦ -(x + 1) * profile x) atTop (𝓝 0) := by
    simpa only [add_mul, neg_mul, pow_zero, pow_one, one_mul, add_zero, neg_zero] using
      ((profile_tail 1).add (profile_tail 0)).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hlim, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hlim
  norm_num [profile] at h ⊢
  exact h

-- An affine time dependence suffices: the PDE and the flux are checked at time zero.
private noncomputable def density (c s x : ℝ) : ℝ := (1 + c * s) * profile x

private lemma profile_balance (k : ℕ) (G B loss : ℝ)
    (hi : IntegrableOn (fun x ↦ x ^ k * profile x) (Ioi 2)) (hB : G * profile 2 = B) :
    HasDerivAt (fun s ↦ ∫ x in Ioi 2, x ^ k * density (G - loss) s x)
      ((k : ℝ) * G * (∫ x in Ioi 2, x ^ (k - 1) * profile x) + B * 2 ^ k -
        loss * (∫ x in Ioi 2, x ^ k * profile x)) 0 ∧ (G = 0 → B = 0) := by
  have h₀ : density (G - loss) 0 = profile := by ext x; simp [density]
  have hcont : Continuous profile := continuous_iff_continuousAt.mpr fun x ↦
    (profile_deriv x).continuousAt
  have h := hasDerivAt_moment_of_sizeIndependentGrowth (t := 0) (U := univ)
    (n := density (G - loss)) (nt := fun _ x ↦ (G - loss) * profile x)
    (nx := fun x ↦ -profile x) (bound := fun x ↦ |G - loss| * (x ^ k * profile x))
    (G := G) (B := B) (loss := loss) k (by norm_num) univ_mem
    (by rw [h₀]; exact profile_mass.1) (by simpa only [h₀] using hi)
    (Filter.Eventually.of_forall fun s ↦
      (hcont.const_mul (1 + (G - loss) * s)).aestronglyMeasurable)
    ((hcont.const_mul (G - loss)).aestronglyMeasurable)
    (fun x _ s _ ↦ by
      simpa [density] using
        (((hasDerivAt_id s).const_mul (G - loss)).const_add 1).mul_const (profile x))
    (fun x hx _ _ ↦ by
      have hxp : 0 ≤ x ^ k := pow_nonneg (le_trans (by norm_num) (le_of_lt hx)) _
      have hp : 0 ≤ profile x := (Real.exp_pos (2 - x)).le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hxp, abs_of_nonneg hp]
      exact (mul_left_comm (x ^ k) |G - loss| (profile x)).le)
    (hi.const_mul _) (fun x _ ↦ by rw [h₀]; exact profile_deriv x)
    (by rw [h₀]; exact hcont.continuousWithinAt) (by simpa only [h₀] using profile_tail k)
    (fun x _ ↦ by rw [h₀]; ring) (by simpa only [h₀] using hB)
  simpa only [h₀] using h

-- The zeroth derivative is the boundary flux, with no bulk growth contribution.
example : HasDerivAt (fun s ↦ ∫ x in Ioi 2, density 1 s x) 1 0 := by
  simpa [profile] using (profile_balance 0 1 1 0 (by simpa using profile_mass.1)
    (by simp [profile])).1

-- The first derivative has both terms: 1 * μ₀ + 2 * B = 3.
example : HasDerivAt (fun s ↦ ∫ x in Ioi 2, x * density 1 s x) 3 0 := by
  have h := (profile_balance 1 1 1 0 (by simpa using profile_first.1) (by simp [profile])).1
  norm_num [profile_mass.2] at h
  exact h

-- Zero speed forces the flux to vanish even though the boundary trace is nonzero.
example {B : ℝ} (hB : 0 * profile 2 = B) : B = 0 ∧
    HasDerivAt (fun s ↦ ∫ x in Ioi 2, x * density 0 s x) 0 0 := by
  obtain ⟨hm, hzero⟩ := profile_balance 1 0 B 0 (by simpa using profile_first.1) hB
  have hB₀ := hzero rfl
  exact ⟨hB₀, by simpa [hB₀] using hm⟩

-- Linear loss 2 subtracts 2 * μ₁ = 6 from the positive transport contribution 3.
example : HasDerivAt (fun s ↦ ∫ x in Ioi 2, x * density (-1) s x) (-3) 0 := by
  have h := (profile_balance 1 1 1 2 (by simpa using profile_first.1) (by simp [profile])).1
  norm_num [profile_mass.2, profile_first.2] at h
  exact h

end Chemistry.ParticleBalances
