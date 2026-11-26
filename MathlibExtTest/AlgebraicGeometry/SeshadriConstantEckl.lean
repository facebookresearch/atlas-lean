/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.SeshadriConstantEckl

/-!
# Tests for Eckl's lower bound for the ten-point Seshadri constant

The first test applies the theorem as stated. The second unfolds the supremum and the infimum
that define `seshadriConstant10`: as `3 / 10 < 4 / 13`, some configuration of ten distinct points
`x₀, …, x₉` of `ℂ²` has `3 · ∑ᵢ mult_{xᵢ} f < 10 · deg f` for every nonzero polynomial `f` of
positive total multiplicity at these points. In particular, the supremum is not the value `0`
that `sSup` takes on an empty set of reals.
-/

open MathlibExt.AlgebraicGeometry.SeshadriConstant
open MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

example : (4 / 13 : ℝ) ≤ seshadriConstant10 :=
  eckl2008LowerBound_wanted

/-- Eckl's bound gives ten distinct points of `ℂ²` at which every nonzero polynomial `f` of
positive total multiplicity satisfies `3 · ∑ᵢ mult_{xᵢ} f < 10 · deg f`. -/
example : ∃ x : Fin 10 → AffinePoint, Function.Injective x ∧
    ∀ f : PlanePolynomial, f ≠ 0 → 0 < ∑ i, multiplicity f (x i) →
      3 * ∑ i, multiplicity f (x i) < 10 * f.totalDegree := by
  have h : (3 / 10 : ℝ) < genericSeshadriConstant :=
    lt_of_lt_of_le (by norm_num) eckl2008LowerBound_wanted
  have hne : {r | ∃ x : Fin 10 → AffinePoint, Function.Injective x ∧
      r = affineSeshadriConstant x}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [genericSeshadriConstant, hempty, Real.sSup_empty] at h
    norm_num at h
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  refine ⟨x, hx, fun f hf hpos ↦ ?_⟩
  have hle := csInf_le (bddBelow_seshadriRatios x) ⟨f, hf, hpos, rfl⟩
  have hsum : (0 : ℝ) < ((∑ i, multiplicity f (x i) : ℕ) : ℝ) := by exact_mod_cast hpos
  have key : (3 / 10 : ℝ) < f.totalDegree / ((∑ i, multiplicity f (x i) : ℕ) : ℝ) :=
    lt_of_lt_of_le hlt hle
  rw [lt_div_iff₀ hsum] at key
  have hcast : ((3 * ∑ i, multiplicity f (x i) : ℕ) : ℝ) < ((10 * f.totalDegree : ℕ) : ℝ) := by
    push_cast at key ⊢
    linarith
  exact_mod_cast hcast
