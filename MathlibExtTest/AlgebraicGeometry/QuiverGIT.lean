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
The base-change action is a left action. For one arrow between two
one-dimensional vertices and `θ = (-1, 1)`, the arrow coordinate is a
semi-invariant of weight one and the target vertex is a subrepresentation of
weight `1`; for the opposite weight it rules out numerical semistability.
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

/-- One arrow from vertex `0` to vertex `1`. -/
abbrev oneArrow : FiniteQuiver where
  Vertex := Fin 2
  Arrow := Unit
  source _ := 0
  target _ := 1

/-- The arrow coordinate. -/
noncomputable def arrowCoordinate : CoordinateRing oneArrow (fun _ ↦ 1) ℚ :=
  MvPolynomial.X ⟨(), (0, 0)⟩

/-- For `θ = (-1, 1)` the arrow coordinate is a semi-invariant of weight one. -/
example : IsSemiInvariant oneArrow (fun _ ↦ 1) ℚ ![-1, 1] 1 arrowCoordinate := by
  intro g M
  simp [evaluate, arrowCoordinate, baseChange, determinantCharacter, Matrix.mul_apply,
    Fin.prod_univ_two, Matrix.det_unique]
  ring

/-- For every representation, `W = (0, 1)` is a subrepresentation, of weight `1`
for `θ = (-1, 1)`. -/
example (M : Representation oneArrow (fun _ ↦ 1) ℚ) :
    IsSubrepresentation oneArrow (fun _ ↦ 1) ℚ M ![⊥, ⊤] ∧
      subrepresentationWeight oneArrow (fun _ ↦ 1) ℚ ![-1, 1] ![⊥, ⊤] = 1 := by
  refine ⟨fun a ↦ ?_, ?_⟩
  · simp
  · have hb : Module.finrank ℚ (⊥ : Submodule ℚ (Fin 1 → ℚ)) = 0 := finrank_bot ℚ _
    have ht : Module.finrank ℚ (⊤ : Submodule ℚ (Fin 1 → ℚ)) = 1 := by simp
    simp only [subrepresentationWeight, Fin.sum_univ_two]
    change (-1 : ℤ) * (Module.finrank ℚ (⊥ : Submodule ℚ (Fin 1 → ℚ)) : ℤ) +
      1 * (Module.finrank ℚ (⊤ : Submodule ℚ (Fin 1 → ℚ)) : ℤ) = 1
    rw [hb, ht]
    norm_num

/-- The opposite weight `(1, -1)` is never numerically semistable: `W = (0, 1)`
has weight `-1`. -/
example (M : Representation oneArrow (fun _ ↦ 1) ℚ) :
    ¬ NumericallySemistable oneArrow (fun _ ↦ 1) ℚ ![1, -1] M := by
  intro h
  have := h ![⊥, ⊤] (fun a ↦ by simp)
  have hb : Module.finrank ℚ (⊥ : Submodule ℚ (Fin 1 → ℚ)) = 0 := finrank_bot ℚ _
  have ht : Module.finrank ℚ (⊤ : Submodule ℚ (Fin 1 → ℚ)) = 1 := by simp
  simp only [subrepresentationWeight, Fin.sum_univ_two] at this
  change (0 : ℤ) ≤ (1 : ℤ) * (Module.finrank ℚ (⊥ : Submodule ℚ (Fin 1 → ℚ)) : ℤ) +
    (-1) * (Module.finrank ℚ (⊤ : Submodule ℚ (Fin 1 → ℚ)) : ℤ) at this
  rw [hb, ht] at this
  norm_num at this
