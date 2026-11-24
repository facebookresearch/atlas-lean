/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.FiniteResolution

/-!
# Changing the target of a finite resolution

An additive functor preserving homology sends the augmentation of a finite
resolution to a quasi-isomorphism. If the resolving functor after target
change is isomorphic to the original resolving functor followed by the target
functor, this gives a finite resolution in the new target category without
changing the resolving complex or its support bound.

Unlike `Functor.mapProjectiveResolution`, this construction does not require
the target functor to preserve every projective object. Projectivity of the
particular resolving terms can be supplied later when the resulting finite
resolution is converted to a projective resolution.

## Main declaration

* `CategoryTheory.Abelian.FiniteResolution.mapTarget`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ChainComplex HomologicalComplex

universe vP uP vA uA vB uB

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {i : P ⥤ A} [i.Additive]
variable {j : P ⥤ B} [j.Additive]
variable {X : A}

/-- Change the target category of a finite resolution along an additive
homology-preserving functor. The resolving complex and its bound are
unchanged. -/
noncomputable def mapTarget
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    FiniteResolution j (F.obj X) where
  complex := Q.complex
  augmentation :=
    (Functor.mapHomologicalComplexCompIso e
        (ComplexShape.down ℕ)).inv.app Q.complex ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.augmentation ≫
        (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.down ℕ) 0).hom.app X
  quasiIso := inferInstance
  bound := Q.bound
  isZero_above := Q.isZero_above

/-- Target change leaves the resolving complex unchanged. -/
@[simp]
theorem mapTarget_complex
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    (mapTarget Q F e).complex = Q.complex :=
  rfl

/-- Terms of the target-changed mapped complex are obtained by applying the
new resolving functor to the original resolving terms. -/
@[simp]
theorem mapTarget_mappedComplex_X
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n : ℕ) :
    (mapTarget Q F e).mappedComplex.X n = j.obj (Q.complex.X n) :=
  rfl

/-- Differentials of the target-changed mapped complex are obtained by
applying the new resolving functor. -/
@[simp]
theorem mapTarget_mappedComplex_d
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n m : ℕ) :
    (mapTarget Q F e).mappedComplex.d n m =
      j.map (Q.complex.d n m) :=
  rfl

/-- The target-changed augmentation is the mapped old augmentation, with the
canonical comparisons at its source and target. -/
@[simp]
theorem mapTarget_augmentation
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    (mapTarget Q F e).augmentation =
      (Functor.mapHomologicalComplexCompIso e
        (ComplexShape.down ℕ)).inv.app Q.complex ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.augmentation ≫
          (HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.down ℕ) 0).hom.app X :=
  rfl

/-- Target change preserves the inclusive support bound definitionally. -/
@[simp]
theorem mapTarget_bound
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    (mapTarget Q F e).bound = Q.bound :=
  rfl

/-- The unchanged resolving complex is zero above the unchanged bound. -/
theorem mapTarget_isZero_above
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n : ℕ) (hn : Q.bound < n) :
    IsZero ((mapTarget Q F e).complex.X n) :=
  Q.isZero_above n hn

end CategoryTheory.Abelian.FiniteResolution
