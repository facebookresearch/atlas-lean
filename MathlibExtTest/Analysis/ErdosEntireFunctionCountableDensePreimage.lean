/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimage
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Separation.Basic

/-! # Tests for preimages of countable dense sets under entire functions -/

open MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted

-- The source set includes 1 and excludes 0 regardless of which points are in the target.
example (B : Set ℂ) (hc : B.Countable) (hd : Dense B) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ f ⁻¹' B = (insert 1 B \ {0}) ∧
      f 1 ∈ B ∧ f 0 ∉ B := by
  have hD : Dense (insert (1 : ℂ) B) := hd.mono (Set.subset_insert _ _)
  obtain ⟨f, hf, h⟩ := conjecture_holds (insert 1 B \ {0}) B
    ((hc.insert 1).mono Set.sdiff_subset) (hD.sdiff_singleton 0) hc hd
  exact ⟨f, differentiableOn_univ.mp hf, Set.ext h, (h 1).mpr (by simp),
    fun h₀ => ((h 0).mp h₀).2 (by simp)⟩
