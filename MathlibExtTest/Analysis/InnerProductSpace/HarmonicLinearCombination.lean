/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HarmonicLinearCombination

open Laplacian

/-- Concrete scalars: a combination `2 • f + 3 • g` of harmonic functions
is harmonic. -/
example {f g : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hf0 : Δ f x = 0) (hg0 : Δ g x = 0) :
    Δ ((2 : ℝ) • f + (3 : ℝ) • g) x = 0 :=
  MathlibExt.Analysis.laplacian_linear_combination_eq_zero hf hg hf0 hg0

/-- Boundary case: the zero combination `0 • f + 0 • g` is harmonic. -/
example {f g : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hf0 : Δ f x = 0) (hg0 : Δ g x = 0) :
    Δ ((0 : ℝ) • f + (0 : ℝ) • g) x = 0 :=
  MathlibExt.Analysis.laplacian_linear_combination_eq_zero hf hg hf0 hg0

/-- Concrete harmonic functions: constants are harmonic, so
`2 • (fun _ => 5) + 3 • (fun _ => 7)` is harmonic everywhere. -/
example (x : EuclideanSpace ℝ (Fin 3)) :
    Δ ((2 : ℝ) • (fun _ : EuclideanSpace ℝ (Fin 3) => (5 : ℝ))
      + (3 : ℝ) • (fun _ : EuclideanSpace ℝ (Fin 3) => (7 : ℝ))) x = 0 := by
  apply MathlibExt.Analysis.laplacian_linear_combination_eq_zero
    (contDiffAt_const) (contDiffAt_const) <;> simp
