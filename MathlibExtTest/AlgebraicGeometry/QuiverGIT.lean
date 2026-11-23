/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.QuiverGIT

/-!
# Tests for quiver character semistability

Character semistability tests semi-invariance on rational points, so it is
only defined over infinite fields: over `𝔽₂` every determinant character is
trivial and the constant `1` would make every representation semistable.
The base-change action is a left action.
-/

noncomputable section

open MathlibExt.AlgebraicGeometry.QuiverGIT

/-- Character semistability cannot be formed over the finite field `𝔽₂`. -/
example (Q : FiniteQuiver) (d : Q.Vertex → ℕ) (θ : Q.Vertex → ℤ)
    (M : Representation Q d (ZMod 2)) : True := by
  fail_if_success
    let _P : Prop := CharacterSemistable Q d (ZMod 2) θ M
  trivial

/-- Over the rationals it is a predicate on representations. -/
example (Q : FiniteQuiver) (d : Q.Vertex → ℕ) (θ : Q.Vertex → ℤ)
    (M : Representation Q d ℚ) : Prop :=
  CharacterSemistable Q d ℚ θ M

/-- A semi-invariant of weight zero for the zero character: the constant `1`
is semi-invariant, so every representation is semistable for `θ = 0`. -/
example (Q : FiniteQuiver) (d : Q.Vertex → ℕ) (M : Representation Q d ℚ) :
    CharacterSemistable Q d ℚ 0 M := by
  refine ⟨1, one_pos, 1, fun g N ↦ ?_, by simp [evaluate]⟩
  simp [evaluate, determinantCharacter]

/-- Base change is a left action. -/
example (Q : FiniteQuiver) (d : Q.Vertex → ℕ) (g h : BaseChangeGroup Q d ℚ)
    (M : Representation Q d ℚ) :
    baseChange Q d ℚ (g * h) M = baseChange Q d ℚ g (baseChange Q d ℚ h M) :=
  baseChange_mul Q d ℚ g h M
