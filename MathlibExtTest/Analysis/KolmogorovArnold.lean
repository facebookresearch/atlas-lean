/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.KolmogorovArnold
import Mathlib.Algebra.BigOperators.Fin

open MathlibExt.Analysis.KolmogorovArnoldWanted.Analysis
open scoped BigOperators

-- A one-dimensional function that jumps immediately outside the closed interval.
example : ∃ (g : ℝ → ℝ) (φ : Fin 3 → ℝ → ℝ),
    Continuous g ∧ (∀ k, Continuous (φ k)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t + 1 = ∑ k, g (φ k t) := by
  classical
  let cube := Set.Icc (0 : Fin 1 → ℝ) 1
  let f (x : Fin 1 → ℝ) := if x ∈ cube then x 0 + 1 else 0
  have hf : ContinuousOn f cube :=
    ((continuous_apply 0).add continuous_const).continuousOn.congr (fun x hx => ite_eq_left hx)
  obtain ⟨g, φ, hg, hφ, heq⟩ := kolmogorov_arnold 1 le_rfl f hf
  refine ⟨g, fun k => φ k 0, hg, fun k => hφ k 0, ?_⟩
  intro t ht
  have hx : (fun _ : Fin 1 => t) ∈ cube := ⟨fun _ => ht.1, fun _ => ht.2⟩
  simpa [f, hx] using heq _ hx

-- A product of two coordinates uses the same outer function in all five summands.
example : ∃ (g : ℝ → ℝ) (φ : Fin 5 → Fin 2 → ℝ → ℝ),
    Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
    ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
      x 0 * x 1 = ∑ k, g (φ k 0 (x 0) + φ k 1 (x 1)) := by
  simpa only [Fin.sum_univ_two] using
    kolmogorov_arnold 2 (by decide) (fun x => x 0 * x 1)
      (((continuous_apply 0).mul (continuous_apply 1)).continuousOn)
