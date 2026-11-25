/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves

/-!
# Tests for the divisorial sheaves `𝒪_X(D)`

The inclusions `𝒪_X(D) ⟶ 𝒪_X(E)` for `D ≤ E` are compatible with the inclusions into `𝒦_X`
and compose, and enlarging the divisor enlarges the sections.
-/

open AlgebraicGeometry MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
open MathlibExt.AlgebraicGeometry.RationalFunctionModules

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]

example {D E F : IntegerWeil V} (h : ∀ p, D p ≤ E p) (h' : ∀ p, E p ≤ F p) :
    CategoryTheory.CategoryStruct.comp (ofLE V h) (ofLE V h') =
      ofLE V (fun p ↦ (h p).trans (h' p)) :=
  rfl

example {D E : IntegerWeil V} (h : ∀ p, D p ≤ E p) :
    CategoryTheory.CategoryStruct.comp (ofLE V h) (inclusion V E) = inclusion V D := by
  simp

/-- A section of `𝒪_X(D)` is a section of `𝒪_X(E)` when `D ≤ E`. -/
example {D E : IntegerWeil V} (h : ∀ p, D p ≤ E p) (U : V.X.left.Opens)
    (s : Γ(rationalFunctions V.X.left, U))
    (hs : s ∈ sections V D U) : s ∈ sections V E U := by
  intro p hp
  rcases hs p hp with h₀ | h₁
  · exact Or.inl h₀
  · exact Or.inr ((neg_le_neg (h p)).trans h₁)
