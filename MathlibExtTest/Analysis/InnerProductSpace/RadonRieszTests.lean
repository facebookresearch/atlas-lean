/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.RadonRiesz
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tests for the Radon–Riesz theorem

* Inner-product form: `1 + 1 / (n + 1)` in `ℝ` converges in norm to `1`.
* Dual-functionals form: same sequence, via an arbitrary continuous linear
  functional.
* `toWeakSpace` form: the constant sequence `5` in `ℝ`.
* The iff form: norm convergence of `1 + 1 / (n + 1)` implies convergence
  of its inner products against every vector.
* Generic Hilbert-space check: a constant sequence converges in norm.
-/

open Set Filter Topology
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.RadonRiesz

namespace MathlibExtTest.Analysis.InnerProductSpace.RadonRieszTests

/-- Inner-product form: `1 + 1 / (n + 1)` converges in norm to `1` in `ℝ`. -/
example : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
  have hu : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have hinner : ∀ y : ℝ,
      Tendsto (fun n : ℕ => ⟪(1 : ℝ) + 1 / (n + 1), y⟫_ℝ) atTop
        (𝓝 ⟪(1 : ℝ), y⟫_ℝ) :=
    fun y => hu.inner tendsto_const_nhds
  have hnorm : Tendsto (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) atTop (𝓝 ‖(1 : ℝ)‖) := by
    have heq : (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) =
        fun n : ℕ => (1 : ℝ) + 1 / (n + 1) :=
      funext fun n : ℕ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [heq]
    simpa using hu
  exact tendsto_of_tendsto_inner_and_tendsto_norm hinner hnorm

/-- Dual-functionals form: `1 + 1 / (n + 1)` converges in norm to `1` in `ℝ`. -/
example : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
  have hu : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  have hdual : ∀ f : StrongDual ℝ ℝ,
      Tendsto (fun n : ℕ => f ((1 : ℝ) + 1 / (n + 1))) atTop (𝓝 (f 1)) :=
    fun f => (f.continuous.tendsto 1).comp hu
  have hnorm : Tendsto (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) atTop (𝓝 ‖(1 : ℝ)‖) := by
    have heq : (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) =
        fun n : ℕ => (1 : ℝ) + 1 / (n + 1) :=
      funext fun n : ℕ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [heq]
    simpa using hu
  exact tendsto_of_forall_tendsto_and_tendsto_norm hdual hnorm

/-- `toWeakSpace` form: the constant sequence `5` in `ℝ` converges in norm. -/
example : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5) :=
  tendsto_of_tendsto_weakSpace_and_tendsto_norm (𝕜 := ℝ) (H := ℝ)
    (u := fun _ : ℕ => (5 : ℝ)) (x := (5 : ℝ)) tendsto_const_nhds tendsto_const_nhds

/-- Iff form: norm convergence implies convergence of the inner products. -/
example : ∀ y : ℝ,
    Tendsto (fun n : ℕ => ⟪(1 : ℝ) + 1 / (n + 1), y⟫_ℝ) atTop
      (𝓝 ⟪(1 : ℝ), y⟫_ℝ) := by
  have hT : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  exact (tendsto_iff_tendsto_inner_and_tendsto_norm (𝕜 := ℝ) (H := ℝ)).mp hT |>.1

/-- Generic check: a constant sequence in any real inner product space
converges in norm via the inner-product form. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : H) :
    Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := by
  apply tendsto_of_tendsto_inner_and_tendsto_norm (𝕜 := ℝ) (H := H)
    (u := fun _ : ℕ => x) (x := x)
  · intro y
    exact tendsto_const_nhds
  · exact tendsto_const_nhds

end MathlibExtTest.Analysis.InnerProductSpace.RadonRieszTests
