/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FraserKakeya
import Mathlib.Data.ZMod.Basic

/-!
# Tests for finite-field Kakeya sets

The three points on the coordinate axes in the binary plane support a measure with Fourier
decay. Its coefficient at zero is one, as required by the normalization of the transform.
-/

open MathlibExt.Combinatorics.FraserKakeyaWanted.Combinatorics.FraserKakeyaProblem

private def axes : Set (Space (ZMod 2) 2) := {x | x 0 = 0 ∨ x 1 = 0}

private theorem axes_kakeya : IsKakeya axes := by
  have lines : ∀ v : Space (ZMod 2) 2, ∃ y : Space (ZMod 2) 2, ∀ a : ZMod 2,
      y 0 + a * v 0 = 0 ∨ y 1 + a * v 1 = 0 := by decide
  intro v
  obtain ⟨y, hy⟩ := lines v
  refine ⟨y, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact hy a

example (χ : AddChar (ZMod 2) ℂ) (hχ : χ ≠ 1) :
    ∃ μ : Space (ZMod 2) 2 → ℝ, IsProbabilityMeasureOn axes μ ∧
      fourier χ μ 0 = 1 ∧ ∀ ξ ≠ 0, ‖fourier χ μ ξ‖ ≤ (2 : ℝ)⁻¹ := by
  obtain ⟨μ, hμ, hdecay⟩ :=
    (fraser_kakeya_fourier_decay_and_sharp.{0, 0} (by decide) axes_kakeya χ hχ).1
  refine ⟨μ, hμ, ?_, ?_⟩
  · simp [fourier, dot, ← Complex.ofReal_sum, hμ.2.1]
  · simpa using hdecay

-- The zero direction contributes just the base point, including in the line average.
example {F : Type*} [Field F] {d : ℕ} (y : Space F d) :
    affineLine y 0 = {y} := by
  ext x
  simp [affineLine]
