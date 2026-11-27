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
# Changing the resolving category of a finite resolution

For preadditive categories P and Q, an abelian category A, additive resolving functors i : P → A
and j : Q → A, an additive functor F : P → Q and a natural isomorphism jF ≅ i carry each finite
i-resolution R of X to a finite j-resolution of X. Its complex has terms F(Rₙ) and differentials
F(d_R), its augmentation is the comparison jF(R) ≅ i(R) followed by the augmentation of R, and
its inclusive support bound remains R.bound.
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

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
mapSource R F e is a finite resolution of the same object X relative to j. Its resolving complex
is F(R), its augmentation jF(R) → X[0] is e_R followed by ε_R, and its inclusive support bound
equals R.bound. -/
def mapSource (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) : FiniteResolution j X where
  complex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex
  augmentation :=
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)).hom.app R.complex ≫
      R.augmentation
  quasiIso := inferInstance
  bound := R.bound
  isZero_above n hn := F.map_isZero (R.isZero_above n hn)

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
the complex underlying mapSource R F e is the image chain complex F(R.complex), indexed by the
natural numbers. -/
theorem mapSource_complex (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) :
    (R.mapSource F e).complex =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex :=
  rfl

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
the degree-n term of mapSource R F e equals F(Rₙ), for every natural number n. -/
theorem mapSource_complex_X (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n : ℕ) :
    (R.mapSource F e).complex.X n = F.obj (R.complex.X n) :=
  rfl

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
the differential from degree n to degree m of mapSource R F e is F(d_R,n,m), for every pair of
natural numbers n and m. -/
theorem mapSource_complex_d (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n m : ℕ) :
    (R.mapSource F e).complex.d n m = F.map (R.complex.d n m) :=
  rfl

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
the augmentation of mapSource R F e is the composite jF(R) → i(R) → X[0], where the first map is
the chain-complex isomorphism induced by e and the second is the augmentation ε_R. -/
theorem mapSource_augmentation (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) :
    (R.mapSource F e).augmentation =
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)).hom.app R.complex ≫
        R.augmentation :=
  rfl

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i,
the inclusive support bound of mapSource R F e equals R.bound. -/
theorem mapSource_bound (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) : (R.mapSource F e).bound = R.bound :=
  rfl

/-- Let P and Q be preadditive categories, A abelian, i : P → A and j : Q → A additive, F : P → Q
additive, and e : jF ≅ i a natural isomorphism. For a finite resolution R of X relative to i, if
the natural number n satisfies R.bound < n, the degree-n term F(Rₙ) of mapSource R F e is a zero
object of Q. -/
theorem mapSource_isZero_above (R : FiniteResolution i X) (F : P ⥤ Q) [F.Additive]
    (e : F ⋙ j ≅ i) (n : ℕ) (hn : R.bound < n) :
    IsZero ((R.mapSource F e).complex.X n) :=
  F.map_isZero (R.isZero_above n hn)

end CategoryTheory.Abelian.FiniteResolution

end
