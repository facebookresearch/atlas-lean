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

Let C be a category with a zero object and zero morphisms, let Z be an object,
and let P be a projective resolution of Z, indexed by the natural numbers.
Its normalization P.zeroNormalized is the resolution concentrated on Z in
degree zero when Z is a zero object, and is P otherwise. Every term of the
normalized resolution is a zero object when Z is zero.

If C is abelian, the chain complexes underlying P.zeroNormalized and P are
homotopy equivalent. The forward comparison preserves their augmentations to
the complex concentrated on Z in degree zero.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

section ZeroObjects

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

/-- Let C be a category with a zero object and zero morphisms, and let Z be a
zero object of C. Then ofIsZero Z is the projective resolution of Z whose chain
complex is concentrated on Z in degree zero, with identity augmentation to
Z[0]. Its positive-degree terms are zero objects. -/
def ofIsZero (Z : C) (hZ : IsZero Z) : ProjectiveResolution Z := by
  let _ : Projective Z := hZ.projective
  exact ProjectiveResolution.self Z

/-- Let C be a category with a zero object and zero morphisms, let Z be a zero
object of C, and let n be a natural number. The degree-n term of the projective
resolution ofIsZero Z is a zero object, including its degree-zero term Z. -/
theorem ofIsZero_complex_X_isZero (Z : C) (hZ : IsZero Z) (n : ℕ) :
    IsZero ((ofIsZero Z hZ).complex.X n) := by
  cases n with
  | zero => simpa [ofIsZero] using hZ
  | succ n =>
      change IsZero (((ChainComplex.single₀ C).obj Z).X (n + 1))
      exact HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 Z (n + 1) (Nat.succ_ne_zero n)

/-- Let C be a category with a zero object and zero morphisms, and let P be a
projective resolution of an object Z. Define P.zeroNormalized to be the
resolution ofIsZero Z concentrated in degree zero if Z is a zero object, and
to be P if Z is not a zero object. Both branches remain resolutions of the
same object Z. -/
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

/-- Let C be a category with a zero object and zero morphisms, let P be a
projective resolution of Z, and assume that Z is a zero object. For every
natural number n, the degree-n term of P.zeroNormalized is a zero object. -/
theorem zeroNormalized_complex_X_isZero {Z : C} (P : ProjectiveResolution Z)
    (hZ : IsZero Z) (n : ℕ) : IsZero (P.zeroNormalized.complex.X n) := by
  rw [P.zeroNormalized_of_isZero hZ]
  exact ofIsZero_complex_X_isZero Z hZ n

end ZeroObjects

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be an abelian category and let P be a projective resolution of an
object Z of C. The natural-number-indexed chain complexes underlying the
specific normalization P.zeroNormalized and P are homotopy equivalent:
P.zeroNormalized.complex ≃ₕ P.complex. The comparison is the projective-resolution
homotopy equivalence between these two resolutions of Z. -/
def zeroNormalizedHomotopyEquiv {Z : C} (P : ProjectiveResolution Z) :
    HomotopyEquiv P.zeroNormalized.complex P.complex :=
  ProjectiveResolution.homotopyEquiv P.zeroNormalized P

/-- Let C be an abelian category, let P be a projective resolution of an object
Z, and let h : P.zeroNormalized.complex → P.complex be the forward map of
P.zeroNormalizedHomotopyEquiv. If π and π₀ are the augmentations of P and
P.zeroNormalized to Z[0], respectively, then h ≫ π = π₀. -/
@[reassoc]
theorem zeroNormalizedHomotopyEquiv_hom_π {Z : C} (P : ProjectiveResolution Z) :
    P.zeroNormalizedHomotopyEquiv.hom ≫ P.π = P.zeroNormalized.π :=
  ProjectiveResolution.homotopyEquiv_hom_π P.zeroNormalized P

end Abelian

end CategoryTheory.ProjectiveResolution

end
