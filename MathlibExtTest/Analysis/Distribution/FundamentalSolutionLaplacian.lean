/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.FundamentalSolutionLaplacian

open Laplacian
open scoped SchwartzMap
open MathlibExt.Analysis.Distribution.NewtonPotentialWanted

-- One distribution recovers evaluation at zero for every test function on Euclidean three-space.
example : ∃ N : 𝓢'(EuclideanSpace ℝ (Fin 3), ℂ),
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ), N (Δ φ) = φ 0 := by
  obtain ⟨N, hN⟩ := exists_fundamental_solution_laplacian
    (E := EuclideanSpace ℝ (Fin 3)) (by simp)
  exact ⟨N, fun φ ↦ by simpa using DFunLike.congr_fun hN φ⟩
