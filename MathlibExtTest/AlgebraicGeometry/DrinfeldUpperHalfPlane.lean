/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DrinfeldUpperHalfPlane
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

open DrinfeldUpperHalfPlane
open scoped MatrixGroups

/-- Source-shaped consumer with the original binders. -/
example (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    (z : K) : z ∈ upperHalfPlane K₀ K ↔ ∀ x : K₀, algebraMap K₀ K x ≠ z :=
  mem_upperHalfPlane_iff K₀ z

/-- Unfolding: the point `i` lies in the Drinfeld upper half plane over `ℚ`. -/
example : Complex.I ∈ upperHalfPlane ℚ ℂ := by
  rw [mem_upperHalfPlane_iff]
  intro x hx
  have h := congrArg Complex.im hx
  simp at h

/-- Nontrivial instance: Möbius action of the identity is the identity. -/
example (z : ℂ) : moebius ℚ ℂ (1 : GL (Fin 2) ℚ) z = z := by
  simp [moebius]

/-- The projective Möbius action preserves the upper half plane at `i`. -/
example : pmoebius ℚ (1 : PGL(2, ℚ)) Complex.I = Complex.I := by
  rw [pmoebius_one]
