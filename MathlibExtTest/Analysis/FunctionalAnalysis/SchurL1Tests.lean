/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.SchurL1

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Tests for Schur's theorem in `ℓ¹`

Concrete checks on `ℓ¹(ℕ, ℂ)`:

* the coordinate evaluation functional and the pairing functional act as
  expected on basis vectors;
* the main theorem applied to the weakly convergent sequence
  `n ↦ (n + 1)⁻¹ • e₀` (which converges in norm to `0` directly, but the
  point of the test is that the weak hypothesis is verified through an
  arbitrary functional, exactly as the theorem consumes it);
* the main theorem applied to a constant sequence.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.SchurL1Tests

open Filter
open scoped Topology ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.SchurL1

/-- The first standard basis vector of `ℓ¹(ℕ, ℂ)`. -/
private noncomputable abbrev e₀ : lp (fun _ : ℕ => ℂ) 1 := lp.single 1 0 1

/-- The coordinate functional at `0` reads off the first coordinate. -/
theorem eval_zero_single (a : ℂ) :
    lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 0 (lp.single 1 0 a) = a := by
  change (lp.single 1 0 a : lp (fun _ : ℕ => ℂ) 1) 0 = a
  rw [lp.single_apply_self]

/-- The coordinate functional at `1` vanishes on the first basis vector. -/
theorem eval_one_single_zero :
    lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 1 e₀ = 0 := by
  change (lp.single 1 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 1) 1 = 0
  rw [lp.single_apply_ne 1 0 1 (by norm_num : (1 : ℕ) ≠ 0)]

/-- Pairing the all-ones sequence with `e₀` gives `1`. -/
theorem dual_ones_single :
    l1DualOfBounded (𝕜 := ℂ) (fun _ => 1) (fun _ => by simp) e₀ = 1 := by
  rw [l1DualOfBounded_apply]
  simp [e₀]

/-- The weakly convergent sequence `n ↦ (n + 1)⁻¹ • e₀` in `ℓ¹(ℕ, ℂ)`. -/
noncomputable def scaledE0 (n : ℕ) : lp (fun _ : ℕ => ℂ) 1 :=
  ((n + 1 : ℝ) : ℂ)⁻¹ • e₀

/-- The sequence `scaledE0` converges weakly to `0`: every functional
applied to it tends to `0`, since the norms tend to `0`. -/
theorem scaledE0_weak (F : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] ℂ) :
    Tendsto (fun n => F (scaledE0 n)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖scaledE0 n‖) atTop (𝓝 0) := by
    have h : ∀ n : ℕ, ‖scaledE0 n‖ = 1 / (n + 1 : ℝ) := by
      intro n
      have he0 : ‖e₀‖ = 1 := by simp [e₀]
      have hnorm1 : ‖((n + 1 : ℝ) : ℂ)⁻¹‖ = 1 / (n + 1 : ℝ) := by
        rw [norm_inv, one_div]
        push_cast
        rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, norm_natCast]
        norm_cast
      simp only [scaledE0, norm_smul, he0, mul_one]
      exact hnorm1
    simp only [h]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h0 : Tendsto scaledE0 atTop (𝓝 (0 : lp (fun _ : ℕ => ℂ) 1)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hF := (F.continuous.tendsto (0 : lp (fun _ : ℕ => ℂ) 1)).comp h0
  simpa only [Function.comp_def, map_zero] using hF

/-- Schur's theorem applied to `scaledE0`: it converges in norm to `0`. -/
theorem schur_scaledE0 :
    Tendsto scaledE0 atTop (𝓝 (0 : lp (fun _ : ℕ => ℂ) 1)) :=
  schur_tendsto_of_weak_tendsto (x := scaledE0) (x₀ := 0) (fun F => by
    simpa using scaledE0_weak F)

/-- Schur's theorem applied to a constant sequence. -/
theorem schur_const (x₀ : lp (fun _ : ℕ => ℂ) 1) :
    Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀) :=
  schur_tendsto_of_weak_tendsto (x := fun _ => x₀) (x₀ := x₀) (fun _ =>
    tendsto_const_nhds)

/-- The norm form of Schur's theorem applied to `scaledE0`. -/
theorem schur_scaledE0_norm :
    Tendsto (fun n => ‖scaledE0 n - (0 : lp (fun _ : ℕ => ℂ) 1)‖) atTop (𝓝 0) :=
  schur_tendsto_norm_sub_of_weak_tendsto (x := scaledE0) (x₀ := 0) (fun F => by
    simpa using scaledE0_weak F)

end MathlibExtTest.Analysis.FunctionalAnalysis.SchurL1Tests
