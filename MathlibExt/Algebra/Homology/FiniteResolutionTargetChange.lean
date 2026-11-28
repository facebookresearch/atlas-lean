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
# Changing the abelian target of a finite resolution

Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, and F : A → B additive
and homology preserving. A natural isomorphism Fi ≅ j sends a finite i-resolution Q of X to a
finite j-resolution of F(X). The resolving complex in P and its support bound remain unchanged;
the augmentation is obtained by applying F to ε_Q and transporting its source and target through
the comparison isomorphisms.
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

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, mapTarget Q F e is a finite resolution of F(X) relative to j. It retains
Q.complex and Q.bound, with augmentation obtained from F(ε_Q) using e⁻¹ on the source and
F(X[0]) ≅ F(X)[0] on the target. -/
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

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, the complex underlying mapTarget Q F e is exactly Q.complex, still indexed by the
natural numbers in P. -/
@[simp]
theorem mapTarget_complex
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    (mapTarget Q F e).complex = Q.complex :=
  rfl

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, the degree-n term of the mapped complex of mapTarget Q F e is j(Qₙ), for every
natural number n. -/
@[simp]
theorem mapTarget_mappedComplex_X
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n : ℕ) :
    (mapTarget Q F e).mappedComplex.X n = j.obj (Q.complex.X n) :=
  rfl

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, the degree-n-to-m differential in the mapped complex of mapTarget Q F e is
j(d_Q,n,m), for every pair of natural numbers n and m. -/
@[simp]
theorem mapTarget_mappedComplex_d
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n m : ℕ) :
    (mapTarget Q F e).mappedComplex.d n m =
      j.map (Q.complex.d n m) :=
  rfl

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, the augmentation of mapTarget Q F e is j(Q) → Fi(Q) → F(X[0]) → F(X)[0]. These
three arrows are the inverse comparison induced by e, the image F(ε_Q), and the canonical
isomorphism for a complex concentrated in degree zero. -/
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

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, the inclusive support bound of mapTarget Q F e equals Q.bound. -/
@[simp]
theorem mapTarget_bound
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) :
    (mapTarget Q F e).bound = Q.bound :=
  rfl

/-- Let P be preadditive, A and B abelian, i : P → A and j : P → B additive, F : A → B additive and
homology preserving, and e : Fi ≅ j a natural isomorphism. For a finite resolution Q of X
relative to i, if Q.bound < n for a natural number n, the degree-n resolving term of mapTarget Q
F e is a zero object of P. -/
theorem mapTarget_isZero_above
    (Q : FiniteResolution i X)
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (e : i ⋙ F ≅ j) (n : ℕ) (hn : Q.bound < n) :
    IsZero ((mapTarget Q F e).complex.X n) :=
  (mapTarget Q F e).isZero_above n hn

end CategoryTheory.Abelian.FiniteResolution
