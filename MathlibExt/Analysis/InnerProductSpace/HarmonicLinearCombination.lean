/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Linear combinations of harmonic functions remain harmonic

If `f` and `g` are twice continuously differentiable at a point `x` and
harmonic there (`Δ f x = 0`, `Δ g x = 0`), then every linear combination
`a • f + b • g` is harmonic there.

## i. Overview

The Laplacian commutes with addition (`ContDiffAt.laplacian_add`) and with
scalar multiplication (`ContDiffAt.laplacian_smul`), so
`Δ (a • f + b • g) x = a • Δ f x + b • Δ g x = 0`.

## ii. Key results

- `MathlibExt.Analysis.laplacian_linear_combination_eq_zero`: linear
  combinations of harmonic functions remain harmonic on their common
  domain.

## iii. References

- `ContDiffAt.laplacian_add`, `ContDiffAt.laplacian_smul` (Mathlib).
-/

@[expose] public section

open Laplacian

namespace MathlibExt.Analysis

/-- Linear combinations of harmonic functions remain harmonic on their
common domain: if `f` and `g` are twice continuously differentiable at `x`
and `Δ f x = 0`, `Δ g x = 0`, then `Δ (a • f + b • g) x = 0`. -/
theorem laplacian_linear_combination_eq_zero {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {a b : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hf0 : Δ f x = 0) (hg0 : Δ g x = 0) :
    Δ (a • f + b • g) x = 0 := by
  have h1 : ContDiffAt ℝ 2 (a • f) x := hf.const_smul a
  have h2 : ContDiffAt ℝ 2 (b • g) x := hg.const_smul b
  rw [h1.laplacian_add h2, InnerProductSpace.laplacian_smul a hf,
    InnerProductSpace.laplacian_smul b hg, hf0, hg0, smul_zero, smul_zero, add_zero]

end MathlibExt.Analysis
