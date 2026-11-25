/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.GaussianSchwartz
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped SchwartzMap
open MathlibExt.Analysis.Distribution.GaussianSchwartzWanted

-- On the real line, extract a weighted bound for the ordinary second derivative.
example : ∃ C : ℝ, ∀ x : ℝ, |x| ^ 3 * |iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (-t ^ 2)) x| ≤ C := by
  obtain ⟨g, hg⟩ := gaussian_mem_schwartz (E := ℝ)
  obtain ⟨C, _, hC⟩ := g.decay 3 2
  refine ⟨C, fun x ↦ ?_⟩
  simpa only [funext hg, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    sq_abs] using hC x

-- In dimension zero the same witness is identically one.
example : ∃ g : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ), ∀ x, g x = 1 := by
  obtain ⟨g, hg⟩ := gaussian_mem_schwartz (E := EuclideanSpace ℝ (Fin 0))
  refine ⟨g, fun x ↦ ?_⟩
  rw [hg, Subsingleton.elim x 0]
  simp
