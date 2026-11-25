/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean`
and
`P2M/Sol/S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.Analysis.Fourier.PoissonSummation

@[expose] public section

open scoped FourierTransform InnerProductSpace SchwartzMap

/-- Consumer with exactly the binders and statement of the source theorem. -/
private theorem exactSource
    {ι : Type*} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) :=
  SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace f x

/-- The same statement at a higher universe, for an index type in `Type 1`. -/
private theorem exactSourceUniverse
    {ι : Type 1} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) :=
  SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace f x

/-- Boundary case: for the zero Schwartz function both lattice sums vanish. -/
example (x : EuclideanSpace ℝ (Fin 2)) :
    ∑' n : Fin 2 → ℤ, (0 : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
        (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) = 0 := by
  rw [SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace]
  simp

/-- The formula at the origin, where every character value is `1`. -/
example (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) :
    ∑' n : Fin 2 → ℤ, f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : Fin 2 → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) := by
  have h := SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace f (0 : EuclideanSpace ℝ (Fin 2))
  simpa using h
