/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.WeakConvergence
public import Mathlib.Analysis.Complex.Basic

/-!
# Tests for weak convergence in normed spaces

* The sequence `1 / (n + 1)` in `ℝ` converges weakly to `0`, so its
  norms are uniformly bounded.
* The sequence `1 + 1 / (n + 1)` in `ℝ` converges weakly to `1`, so
  `‖1‖ ≤ liminf ‖1 + 1 / (n + 1)‖`.
* Bounded operators preserve weak convergence: scaling by `2` sends the
  weakly null sequence `1 / (n + 1)` to a weakly null sequence.
* The `toWeakSpace` forms, on the constant sequence `5` in `ℝ`.
* The complex case: `1 / (n + 1)` in `ℂ` is norm-bounded.
-/

namespace MathlibExtTest.Analysis.Normed.Module.WeakConvergenceTests

open Set Filter Topology
open MathlibExt.Analysis.Normed.Module.WeakConvergence

/-- Weak convergence of `1 / (n + 1)` in `ℝ` implies boundedness of its norms. -/
example : BddAbove (Set.range fun n : ℕ => ‖(1 : ℝ) / (n + 1)‖) := by
  apply bddAbove_norm_range_of_forall_tendsto (𝕜 := ℝ) (E := ℝ)
  intro f
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (f.continuous.tendsto 0).comp hlim

/-- Weak lower semicontinuity of the norm for `1 + 1 / (n + 1)` in `ℝ`. -/
example : ‖(1 : ℝ)‖ ≤ liminf (fun n : ℕ => ‖(1 : ℝ) + 1 / (n + 1)‖) atTop := by
  apply norm_le_liminf_norm_of_forall_tendsto (𝕜 := ℝ) (E := ℝ)
  intro f
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
  exact (f.continuous.tendsto 1).comp hlim

/-- Scaling by `2` preserves weak convergence of `1 / (n + 1)` in `ℝ`. -/
example : ∀ g : StrongDual ℝ ℝ,
    Tendsto (fun n : ℕ => g ((2 : ℝ) • ((1 : ℝ) / (n + 1)))) atTop (𝓝 (g 0)) := by
  intro g
  have hweak : ∀ f : StrongDual ℝ ℝ,
      Tendsto (fun n : ℕ => f ((1 : ℝ) / (n + 1))) atTop (𝓝 (f 0)) := by
    intro f
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (f.continuous.tendsto 0).comp hlim
  have h := tendsto_apply_of_forall_tendsto (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) hweak g
  simpa using h

/-- Boundedness, `toWeakSpace` form, for the constant sequence `5` in `ℝ`. -/
example : BddAbove (Set.range fun _ : ℕ => ‖(5 : ℝ)‖) :=
  bddAbove_norm_range_of_tendsto_weakSpace (𝕜 := ℝ) (E := ℝ) tendsto_const_nhds

/-- Lower semicontinuity, `toWeakSpace` form, for the constant sequence `5` in `ℝ`. -/
example : ‖(5 : ℝ)‖ ≤ liminf (fun _ : ℕ => ‖(5 : ℝ)‖) atTop :=
  norm_le_liminf_norm_of_tendsto_weakSpace (𝕜 := ℝ) (E := ℝ) tendsto_const_nhds

/-- The complex case: `1 / (n + 1)` in `ℂ` is norm-bounded. -/
example : BddAbove (Set.range fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1)‖) := by
  apply bddAbove_norm_range_of_forall_tendsto (𝕜 := ℂ) (E := ℂ)
  intro f
  have hlim : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (f.continuous.tendsto 0).comp hlim

end MathlibExtTest.Analysis.Normed.Module.WeakConvergenceTests
