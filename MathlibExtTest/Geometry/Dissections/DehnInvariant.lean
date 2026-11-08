/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Dissections.DehnInvariant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Tests for the Dehn invariant

Boundary cases (empty list, zero length, zero angle, concatenation), the cube
value at concrete edge lengths, the tetrahedron value under the irrationality
hypothesis, and the nonvanishing criterion at a concrete irrational angle
`π * √2`, where irrationality of `√2` is known.
-/

@[expose] public section

namespace MathlibExtTest.Geometry.Dissections.DehnInvariant

-- `_root_` disambiguates from this file's own `...Dissections.DehnInvariant` namespace.
open Real _root_.DehnInvariant

/-- Empty edge list: Dehn invariant `0`, by `simp`. -/
example : dehnInvariant [] = 0 := by simp

/-- A zero-length edge contributes `0`, by `simp`. -/
example : dehnInvariant [⟨0, π⟩] = 0 := by simp [dehnInvariant]

/-- A zero-angle edge contributes `0`, by `simp`. -/
example : dehnInvariant [⟨1, 0⟩] = 0 := by simp [dehnInvariant]

/-- Concatenation adds Dehn invariants, by `simp`. -/
example (e₁ e₂ : List Edge) :
    dehnInvariant (e₁ ++ e₂) = dehnInvariant e₁ + dehnInvariant e₂ := by simp

/-- The cube has Dehn invariant `0` at concrete edge lengths. -/
example : dehnInvariant (cubeEdges 1) = 0 := dehnInvariant_cubeEdges 1

example : dehnInvariant (cubeEdges 2) = 0 := dehnInvariant_cubeEdges 2

/-- Two cubes concatenated still have Dehn invariant `0`. -/
example : dehnInvariant (cubeEdges 1 ++ cubeEdges 2) = 0 := by
  simp [dehnInvariant_cubeEdges]

/-- The tetrahedron has nonzero Dehn invariant under the irrationality hypothesis. -/
example (hirr : Irrational (tetrahedralAngle / π)) :
    dehnInvariant (tetrahedronEdges 1) ≠ 0 :=
  dehnInvariant_tetrahedronEdges_ne_zero one_ne_zero hirr

/-- Cube and tetrahedron have different Dehn invariants under the hypothesis. -/
example (hirr : Irrational (tetrahedralAngle / π)) :
    dehnInvariant (cubeEdges 1) ≠ dehnInvariant (tetrahedronEdges 1) :=
  dehnInvariant_cube_ne_dehnInvariant_tetrahedron one_ne_zero hirr

/-- The nonvanishing criterion at the concrete angle `π * √2`: `(π * √2) / π = √2`
is irrational. -/
example : (1 : ℝ) ⊗ₜ[ℤ] (↑(π * Real.sqrt 2) : AddCircle (2 * π)) ≠ 0 := by
  apply tmul_ne_zero_of_irrational one_ne_zero
  have h : (π * Real.sqrt 2) / π = Real.sqrt 2 := by
    field_simp
  rw [h]
  exact irrational_sqrt_two

/-- The separating `ℚ`-linear map exists at the concrete angle `π * √2`. -/
example : ∃ f : ℝ →ₗ[ℚ] ℝ, f π = 0 ∧ f (π * Real.sqrt 2) ≠ 0 := by
  apply exists_linearMap_of_irrational
  have h : (π * Real.sqrt 2) / π = Real.sqrt 2 := by
    field_simp
  rw [h]
  exact irrational_sqrt_two

end MathlibExtTest.Geometry.Dissections.DehnInvariant
