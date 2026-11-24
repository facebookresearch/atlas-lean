/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolution

/-!
# Changing the resolving category of an finite resolution

An additive functor `F : P ⥤ Q` and an compatibility isomorphism `F ⋙ j ≅ i` carry an original
`i`-resolution to a `j`-resolution. Its resolving complex is the image complex under `F`, and its
augmentation uses the canonical homological-complex comparison followed by the original
augmentation. Its inclusive support bound is unchanged.

This complements the existing target-change constructor. No projective- dimension,
resolution-equivalence, or K-theory outcome is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] {j : Q ⥤ A} [j.Additive] {X : A}

/--
Map the original resolving complex along the additive source functor, retaining the original bound
and canonical augmentation program.
-/
def mapSource (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) : FiniteResolution j X where
  complex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex
  augmentation :=
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)).hom.app R.complex ≫
      R.augmentation
  quasiIso := inferInstance
  bound := R.bound
  isZero_above n hn := F.map_isZero (R.isZero_above n hn)

/-- The whole resolving complex is the image of the original complex. -/
theorem mapSource_complex (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) :
    (R.mapSource F e).complex =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex :=
  rfl

/-- Every resolving term is the original source-functor image term. -/
theorem mapSource_complex_X (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n : ℕ) :
    (R.mapSource F e).complex.X n = F.obj (R.complex.X n) :=
  rfl

/-- Every differential is the original source-functor image of the original differential. -/
theorem mapSource_complex_d (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n m : ℕ) :
    (R.mapSource F e).complex.d n m = F.map (R.complex.d n m) :=
  rfl

/-- The entire augmentation is the canonical comparison followed by
the unchanged original augmentation. -/
theorem mapSource_augmentation (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) :
    (R.mapSource F e).augmentation =
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)).hom.app R.complex ≫
        R.augmentation :=
  rfl

/-- Source change retains the sharp original inclusive support bound. -/
theorem mapSource_bound (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) : (R.mapSource F e).bound = R.bound :=
  rfl

/-- Original zero terms above the original bound map to zero terms. -/
theorem mapSource_isZero_above (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n : ℕ) (hn : R.bound < n) :
    IsZero ((R.mapSource F e).complex.X n) :=
  F.map_isZero (R.isZero_above n hn)

end CategoryTheory.Abelian.FiniteResolution

end
