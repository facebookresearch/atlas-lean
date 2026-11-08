/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.KadecKlee
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tests for the Kadec–Klee property in uniformly convex spaces

* All-functionals form: `1 + 1 / (n + 1)` in `ℝ` converges in norm to `1`.
* All-functionals form, zero limit: `1 / (n + 1)` in `ℝ` converges in norm
  to `0` (the `x = 0` branch of the proof).
* `toWeakSpace` form: the constant sequence `5` in `ℝ`.
* The iff form: norm convergence of `1 + 1 / (n + 1)` implies weak
  convergence plus convergence of the norms.
* Generic check: a constant sequence in any uniformly convex space
  converges in norm.
-/

open Set Filter Topology
open MathlibExt.Analysis.Normed.Module.KadecKlee

namespace MathlibExtTest.Analysis.Normed.Module.KadecKleeTests

/-- All-functionals form: `1 + 1 / (n + 1)` converges in norm to `1` in `ℝ`. -/
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

/-- All-functionals form, zero limit: `1 / (n + 1)` converges in norm to `0` in `ℝ`. -/
example : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdual : ∀ f : StrongDual ℝ ℝ,
      Tendsto (fun n : ℕ => f ((1 : ℝ) / (n + 1))) atTop (𝓝 (f 0)) :=
    fun f => (f.continuous.tendsto 0).comp hu
  have hnorm : Tendsto (fun n : ℕ => ‖(1 : ℝ) / (n + 1)‖) atTop (𝓝 ‖(0 : ℝ)‖) := by
    simp only [norm_zero]
    have heq : (fun n : ℕ => ‖(1 : ℝ) / (n + 1)‖) = fun n : ℕ => (1 : ℝ) / (n + 1) :=
      funext fun n : ℕ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [heq]
    exact hu
  exact tendsto_of_forall_tendsto_and_tendsto_norm hdual hnorm

/-- `toWeakSpace` form: the constant sequence `5` in `ℝ` converges in norm. -/
example : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5) :=
  tendsto_of_tendsto_weakSpace_and_tendsto_norm tendsto_const_nhds tendsto_const_nhds

/-- Iff form: norm convergence implies weak convergence plus convergence
of the norms. -/
example : (∀ f : StrongDual ℝ ℝ,
    Tendsto (fun n : ℕ => f ((1 : ℝ) + 1 / (n + 1))) atTop (𝓝 (f 1))) ∧
    Tendsto (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) atTop (𝓝 ‖(1 : ℝ)‖) := by
  have hT : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  exact tendsto_iff_forall_tendsto_and_tendsto_norm.mp hT

/-- Generic check: a constant sequence in any uniformly convex space
converges in norm via the all-functionals form. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]
    (x : E) :
    Tendsto (fun _ : ℕ => x) atTop (𝓝 x) :=
  tendsto_of_forall_tendsto_and_tendsto_norm (fun _ => tendsto_const_nhds)
    tendsto_const_nhds

end MathlibExtTest.Analysis.Normed.Module.KadecKleeTests
