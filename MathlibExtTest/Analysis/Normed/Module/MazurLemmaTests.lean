/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.MazurLemma
public import Mathlib.Analysis.Complex.Basic

/-!
# Tests for Mazur's lemma

* The sequence `1 / (n + 1)` in `ℝ` converges weakly to `0`, so a finite
  convex combination of its tail terms (from `n ≥ 2`) is within `1 / 2`
  of `0`.
* The same sequence in `ℂ` converges weakly to `0`, exercising the
  complex case.
* A two-dimensional sequence `(1 / (n + 1), 0)` in `ℝ × ℝ` converges
  weakly to `(0, 0)`, so a finite convex combination of its terms is
  within `1 / 4` of `(0, 0)`.
* The hull form: `0` lies in the norm closure of the convex hull of the
  range of `1 / (n + 1)`.
-/

namespace MathlibExtTest.Analysis.Normed.Module.MazurLemmaTests

open Set Filter Topology
open MathlibExt.Analysis.Normed.Module.MazurLemma

/-- The sequence `1 / (n + 1)` in `ℝ` converges weakly to `0`. -/
example : ∀ f : StrongDual ℝ ℝ,
    Filter.Tendsto (fun n : ℕ => f ((1 : ℝ) / (n + 1))) Filter.atTop
      (𝓝 (f 0)) := by
  intro f
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (f.continuous.tendsto 0).comp hlim

/-- Mazur's lemma on the tail `n ≥ 2` of `1 / (n + 1)` in `ℝ`. -/
example : ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (n : ι → ℕ),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, 2 ≤ n i) ∧
      ‖∑ i, w i • ((1 : ℝ) / (n i + 1)) - (0 : ℝ)‖ < 1 / 2 := by
  apply exists_finite_convex_combination_norm_sub_lt_of_forall_tendsto
    (𝕜 := ℝ) (E := ℝ)
    (u := fun n : ℕ => (1 : ℝ) / (n + 1)) (x := (0 : ℝ)) (N := 2) (ε := 1 / 2)
  · intro f
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (f.continuous.tendsto 0).comp hlim
  · norm_num

/-- Mazur's lemma for `1 / (n + 1)` in `ℂ`. -/
example : ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (n : ι → ℕ),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, 0 ≤ n i) ∧
      ‖∑ i, w i • ((1 : ℂ) / ((n i : ℂ) + 1)) - (0 : ℂ)‖ < 1 / 4 := by
  apply exists_finite_convex_combination_norm_sub_lt_of_forall_tendsto
    (𝕜 := ℂ) (E := ℂ)
    (u := fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) (x := (0 : ℂ))
    (N := 0) (ε := 1 / 4)
  · intro f
    have hlim : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (f.continuous.tendsto 0).comp hlim
  · norm_num

/-- Mazur's lemma for `(1 / (n + 1), 0)` in `ℝ × ℝ`. -/
example : ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (n : ι → ℕ),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, 0 ≤ n i) ∧
      ‖∑ i, w i • (((1 : ℝ) / (n i + 1)), (0 : ℝ)) - ((0 : ℝ), (0 : ℝ))‖ < 1 / 4 := by
  apply exists_finite_convex_combination_norm_sub_lt_of_forall_tendsto
    (𝕜 := ℝ) (E := ℝ × ℝ)
    (u := fun n : ℕ => ((1 : ℝ) / (n + 1), (0 : ℝ)))
    (x := ((0 : ℝ), (0 : ℝ))) (N := 0) (ε := 1 / 4)
  · intro f
    have hnorm : Tendsto (fun n : ℕ => ‖((1 : ℝ) / (n + 1), (0 : ℝ))‖) atTop
        (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hnorm_eq : (fun n : ℕ => ‖((1 : ℝ) / (n + 1), (0 : ℝ))‖) =
          (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
        funext n
        have h1 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
          div_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg n) zero_le_one)
        simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg h1, abs_zero,
          max_eq_left h1]
      rw [hnorm_eq]
      exact hlim
    have hlim : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1), (0 : ℝ))) atTop
        (𝓝 ((0 : ℝ), (0 : ℝ))) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    exact (f.continuous.tendsto _).comp hlim
  · norm_num

/-- The hull form: `0` is in the closure of the convex hull of the range
of `1 / (n + 1)` in `ℝ`. -/
example : (0 : ℝ) ∈ closure
    (convexHull ℝ (Set.range (fun n : ℕ => (1 : ℝ) / (n + 1)))) := by
  apply mem_closure_convexHull_range_of_tendsto_weakSpace
    (𝕜 := ℝ) (E := ℝ)
    (u := fun n : ℕ => (1 : ℝ) / (n + 1)) (x := (0 : ℝ))
  have hinj : Function.Injective (LinearMap.flip (topDualPairing ℝ ℝ)) := by
    intro a b hab
    exact SeparatingDual.eq_iff_forall_dual_eq.mpr fun f =>
      congrFun (congrArg DFunLike.coe hab) f
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ ℝ).flip hinj).mpr ?_
  intro f
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (f.continuous.tendsto 0).comp hlim

end MathlibExtTest.Analysis.Normed.Module.MazurLemmaTests
