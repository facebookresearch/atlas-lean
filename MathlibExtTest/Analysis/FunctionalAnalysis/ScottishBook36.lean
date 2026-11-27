/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36

open Metric MathlibExt.Analysis.FunctionalAnalysis.ScottishBook36Wanted
open scoped lp

-- Restrict the map to the closed ball in a Hilbert space with uncountably many basis vectors.
example : ∃ r : closedBall (0 : ℓ²(ℝ, ℝ)) 1 → sphere (0 : ℓ²(ℝ, ℝ)) 1,
    Continuous r ∧ Function.LeftInverse r (Set.inclusion sphere_subset_closedBall) := by
  have hdim : ¬ Module.Finite ℝ ℓ²(ℝ, ℝ) := by
    intro h
    have b := (default : HilbertBasis ℝ ℝ ℓ²(ℝ, ℝ)).orthonormal.linearIndependent
    exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℝ)) b.finite
  obtain ⟨f, hf, hs, hfix⟩ := hilbertBallRetractsOntoSphere ℓ²(ℝ, ℝ) hdim
  exact ⟨fun x => ⟨f x, hs x⟩, (hf.comp continuous_subtype_val).subtype_mk _,
    fun x => Subtype.ext (hfix x x.property)⟩
