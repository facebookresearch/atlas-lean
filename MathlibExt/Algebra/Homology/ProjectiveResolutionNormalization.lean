/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Projective resolutions normalized at zero objects

A supplied projective resolution can be replaced by the degree-zero resolution when its resolved
object is zero, while retaining it otherwise. Every term of the zero branch is zero. The
construction needs only zero objects and zero morphisms; the homotopy comparisons additionally
require an abelian category.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

section ZeroObjects

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- The projective resolution concentrated in degree zero on a zero object. -/
def ofIsZero (Z : C) (hZ : IsZero Z) : ProjectiveResolution Z := by
  let _ : Projective Z := hZ.projective
  exact ProjectiveResolution.self Z

/-- Every term of the projective resolution of a zero object is zero. -/
theorem ofIsZero_complex_X_isZero (Z : C) (hZ : IsZero Z) (n : ℕ) :
    IsZero ((ofIsZero Z hZ).complex.X n) := by
  cases n with
  | zero => simpa [ofIsZero] using hZ
  | succ n =>
      change IsZero (((ChainComplex.single₀ C).obj Z).X (n + 1))
      exact HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 Z (n + 1) (Nat.succ_ne_zero n)

/-- Normalize a supplied resolution at zero objects, retaining it otherwise. -/
def zeroNormalized {Z : C} (P : ProjectiveResolution Z) : ProjectiveResolution Z := by
  classical
  exact if hZ : IsZero Z then ofIsZero Z hZ else P

@[simp]
theorem zeroNormalized_of_isZero {Z : C} (P : ProjectiveResolution Z)
    (hZ : IsZero Z) : P.zeroNormalized = ofIsZero Z hZ := by
  simp [zeroNormalized, hZ]

@[simp]
theorem zeroNormalized_of_not_isZero {Z : C} (P : ProjectiveResolution Z)
    (hZ : ¬ IsZero Z) : P.zeroNormalized = P := by
  simp [zeroNormalized, hZ]

/-- Every term of a normalized resolution of a zero object is zero. -/
theorem zeroNormalized_complex_X_isZero {Z : C} (P : ProjectiveResolution Z)
    (hZ : IsZero Z) (n : ℕ) : IsZero (P.zeroNormalized.complex.X n) := by
  rw [P.zeroNormalized_of_isZero hZ]
  exact ofIsZero_complex_X_isZero Z hZ n

end ZeroObjects

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The normalized resolution is homotopy equivalent to the supplied one. -/
def zeroNormalizedHomotopyEquiv {Z : C} (P : ProjectiveResolution Z) :
    HomotopyEquiv P.zeroNormalized.complex P.complex :=
  ProjectiveResolution.homotopyEquiv P.zeroNormalized P

/-- The normalization comparison commutes with the augmentations. -/
@[reassoc]
theorem zeroNormalizedHomotopyEquiv_hom_π {Z : C} (P : ProjectiveResolution Z) :
    P.zeroNormalizedHomotopyEquiv.hom ≫ P.π = P.zeroNormalized.π :=
  ProjectiveResolution.homotopyEquiv_hom_π P.zeroNormalized P

end Abelian

end CategoryTheory.ProjectiveResolution

end
