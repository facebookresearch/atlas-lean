/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.MemLpTruncation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Tests for `L^p` membership via truncated integrals

* The constant function `1` lies in `L^2 ([0, 1])`, by the truncated-integral
  characterization: the truncated integrals are all bounded by `1`.
* The constant function `1` does not lie in `L^2 (ℝ)`, by the same
  characterization: the truncated integrals are unbounded.
* Both conclusions also hold at `p = 1/2`, exercising the public API
  strictly below exponent `1`.
-/

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.MemLpTruncation

namespace MathlibExtTest.MeasureTheory.Function.MemLpTruncationTests

/-- The constant function `1` lies in `L^2 ([0, 1])`. -/
example : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [memLp_iff_iSup_lintegral_Icc_inter_lt_top (by norm_num) (by norm_num)
    (Set.Icc (0 : ℝ) 1) measurableSet_Icc measurable_const]
  refine lt_of_le_of_lt (iSup_le fun n => ?_)
    (show (1 : ℝ≥0∞) < ⊤ from by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_lt_top)
  have h_integrand : ∀ x : ℝ, (‖(1 : ℝ)‖ₑ) ^ (2 : ℝ≥0∞).toReal = 1 := by
    intro x
    simp
  calc ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.Icc (0 : ℝ) 1,
          (‖(1 : ℝ)‖ₑ) ^ (2 : ℝ≥0∞).toReal ∂volume
      = ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂volume := by
        congr 1
        ext x
        exact h_integrand x
    _ ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂volume :=
        lintegral_mono_set Set.inter_subset_right
    _ = 1 := by
        rw [setLIntegral_one]
        simp [Real.volume_Icc]

/-- The constant function `1` does not lie in `L^2 (ℝ)`. -/
example : ¬ MemLp (fun _ : ℝ => (1 : ℝ)) 2 volume := by
  intro h
  have h' : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Set.univ) := by
    rwa [Measure.restrict_univ]
  rw [memLp_iff_iSup_lintegral_Icc_inter_lt_top (by norm_num) (by norm_num)
    Set.univ MeasurableSet.univ measurable_const] at h'
  have hge : ∀ n : ℕ, (n : ℝ≥0∞) ≤
      ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ,
        (‖(1 : ℝ)‖ₑ) ^ (2 : ℝ≥0∞).toReal ∂volume := by
    intro n
    have hsub : Set.Icc (0 : ℝ) n ⊆ Set.Icc (-(n : ℝ)) n ∩ Set.univ := by
      intro x hx
      exact ⟨⟨by linarith [hx.1, hx.2], hx.2⟩, Set.mem_univ x⟩
    calc (n : ℝ≥0∞)
        = ∫⁻ x in Set.Icc (0 : ℝ) n, (1 : ℝ≥0∞) ∂volume := by
          rw [setLIntegral_one]
          simp [Real.volume_Icc]
      _ ≤ ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ, (1 : ℝ≥0∞) ∂volume :=
          lintegral_mono_set hsub
      _ = ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ,
            (‖(1 : ℝ)‖ₑ) ^ (2 : ℝ≥0∞).toReal ∂volume := by
          congr 1
          ext x
          simp
  have htop : (⊤ : ℝ≥0∞) ≤
      ⨆ m : ℕ, ∫⁻ x in Set.Icc (-(m : ℝ)) m ∩ Set.univ,
        (‖(1 : ℝ)‖ₑ) ^ (2 : ℝ≥0∞).toReal ∂volume := by
    rw [← ENNReal.iSup_natCast]
    exact iSup_mono hge
  exact absurd (h'.trans_le htop) (by simp)


/-- The constant function `1` lies in `L^(1/2) ([0, 1])`. -/
example : MemLp (fun _ : ℝ => (1 : ℝ)) (1 / 2) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [memLp_iff_iSup_lintegral_Icc_inter_lt_top (by norm_num) (by norm_num)
    (Set.Icc (0 : ℝ) 1) measurableSet_Icc measurable_const]
  refine lt_of_le_of_lt (iSup_le fun n => ?_)
    (show (1 : ℝ≥0∞) < ⊤ from by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_lt_top)
  have h_integrand : ∀ x : ℝ, (‖(1 : ℝ)‖ₑ) ^ ((1 / 2) : ℝ≥0∞).toReal = 1 := by
    intro x
    simp
  calc ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.Icc (0 : ℝ) 1,
          (‖(1 : ℝ)‖ₑ) ^ ((1 / 2) : ℝ≥0∞).toReal ∂volume
      = ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂volume := by
        congr 1
        ext x
        exact h_integrand x
    _ ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ∂volume :=
        lintegral_mono_set Set.inter_subset_right
    _ = 1 := by
        rw [setLIntegral_one]
        simp [Real.volume_Icc]

/-- The constant function `1` does not lie in `L^(1/2) (ℝ)`. -/
example : ¬ MemLp (fun _ : ℝ => (1 : ℝ)) (1 / 2) volume := by
  intro h
  have h' : MemLp (fun _ : ℝ => (1 : ℝ)) (1 / 2) (volume.restrict Set.univ) := by
    rwa [Measure.restrict_univ]
  rw [memLp_iff_iSup_lintegral_Icc_inter_lt_top (by norm_num) (by norm_num)
    Set.univ MeasurableSet.univ measurable_const] at h'
  have hge : ∀ n : ℕ, (n : ℝ≥0∞) ≤
      ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ,
        (‖(1 : ℝ)‖ₑ) ^ ((1 / 2) : ℝ≥0∞).toReal ∂volume := by
    intro n
    have hsub : Set.Icc (0 : ℝ) n ⊆ Set.Icc (-(n : ℝ)) n ∩ Set.univ := by
      intro x hx
      exact ⟨⟨by linarith [hx.1, hx.2], hx.2⟩, Set.mem_univ x⟩
    calc (n : ℝ≥0∞)
        = ∫⁻ x in Set.Icc (0 : ℝ) n, (1 : ℝ≥0∞) ∂volume := by
          rw [setLIntegral_one]
          simp [Real.volume_Icc]
      _ ≤ ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ, (1 : ℝ≥0∞) ∂volume :=
          lintegral_mono_set hsub
      _ = ∫⁻ x in Set.Icc (-(n : ℝ)) n ∩ Set.univ,
            (‖(1 : ℝ)‖ₑ) ^ ((1 / 2) : ℝ≥0∞).toReal ∂volume := by
          congr 1
          ext x
          simp
  have htop : (⊤ : ℝ≥0∞) ≤
      ⨆ m : ℕ, ∫⁻ x in Set.Icc (-(m : ℝ)) m ∩ Set.univ,
        (‖(1 : ℝ)‖ₑ) ^ ((1 / 2) : ℝ≥0∞).toReal ∂volume := by
    rw [← ENNReal.iSup_natCast]
    exact iSup_mono hge
  exact absurd (h'.trans_le htop) (by simp)

#print axioms lintegral_eq_iSup_lintegral_Icc_inter
#print axioms memLp_iff_iSup_lintegral_Icc_inter_lt_top

end MathlibExtTest.MeasureTheory.Function.MemLpTruncationTests
