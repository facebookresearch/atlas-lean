/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.GradedTensorTower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Equality of graded tensor maps and their descents

Let R be a commutative ring and work with integer-graded R-modules.
Equality of the source and target graded families allows degreewise
heterogeneous equalities of maps to assemble into equality of graded maps.

Assume tensor products of all integer-graded objects exist, with degree-i
term the coproduct of Xᵃ⊗Yᵇ over a+b=i. Equality of the graded families
of two pairs of cochain complexes identifies their tensor terms, and a
family of maps on these antidiagonal summands has the same descent whether
formed from the tensor complex or from its graded tensor object.
The descents respect equality of the factor families, target module and
summand maps.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]

/-- Let R be a commutative ring and X,Y,X′,Y′ integer-graded R-modules.
Given equalities X=X′ and Y=Y′, if graded maps f:X → Y and g:X′ → Y′
have heterogeneously equal components in every integer degree, then the
graded maps themselves are heterogeneously equal. -/
theorem gradedMap_heq
    {X Y X' Y' : GradedObject ℤ (ModuleCat.{u} R)}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : ∀ i : ℤ, HEq (f i) (g i)) : HEq f g := by
  subst X'
  subst Y'
  apply heq_of_eq
  funext i
  exact eq_of_heq (h i)

variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]

/-- Let R be a commutative ring and assume tensor products of all
integer-graded R-modules exist. If integer-indexed cochain complexes
C,C′ have equal graded term families and D,D′ have equal graded term
families, then the tensor cochain complexes C⊗D and C′⊗D′ have equal
graded term families. -/
theorem tensorObj_X_congr
    {C D C' D' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hC : C.X = C'.X) (hD : D.X = D'.X) :
    (HomologicalComplex.tensorObj C D).X = (HomologicalComplex.tensorObj C' D').X := by
  rw [HomologicalComplex.tensorObj_X_eq_graded, HomologicalComplex.tensorObj_X_eq_graded]
  exact GradedObject.Monoidal.tensorObj_eq C.X D.X C'.X D'.X hC hD

/-- Let R be a commutative ring and assume tensor products of all
integer-graded R-modules exist. For integer-indexed cochain complexes
K,L, an R-module M and degree i, give maps
f_{a,b}:Kᵃ⊗Lᵇ → M for every a+b=i.
Their descent from the degree-i tensor-complex term equals their descent
from the graded tensor coproduct over the same antidiagonal. -/
theorem tensorDesc_eq_graded
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (i : ℤ)
    (f : ∀ (a b : ℤ) (_ : a + b = i), K.X a ⊗ L.X b ⟶ M) :
    HomologicalComplex.mapBifunctorDesc (F := curriedTensor (ModuleCat.{u} R))
        (c := ComplexShape.up ℤ) f =
      GradedObject.Monoidal.tensorObjDesc f := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  have hι : HomologicalComplex.ιTensorObj K L a b i hab =
      GradedObject.Monoidal.ιTensorObj K.X L.X a b i hab := rfl
  change f a b hab = HomologicalComplex.ιTensorObj K L a b i hab ≫
    GradedObject.Monoidal.tensorObjDesc f
  rw [hι]
  exact (GradedObject.Monoidal.ι_tensorObjDesc f a b hab).symm

/-- Let R be a commutative ring and assume tensor products of all
integer-graded R-modules exist. Given equal graded families X=X′, Y=Y′
and equal target modules M=M′, suppose two families of maps
Xᵃ⊗Yᵇ → M and X′ᵃ⊗Y′ᵇ → M′ are heterogeneously equal on every
summand a+b=i. Their degree-i graded tensor descents are heterogeneously
equal. -/
theorem gradedDesc_heq
    {X Y X' Y' : GradedObject ℤ (ModuleCat.{u} R)} {M M' : ModuleCat.{u} R} {i : ℤ}
    (hX : X = X') (hY : Y = Y') (hM : M = M')
    (f : ∀ (a b : ℤ) (_ : a + b = i), X a ⊗ Y b ⟶ M)
    (g : ∀ (a b : ℤ) (_ : a + b = i), X' a ⊗ Y' b ⟶ M')
    (h : ∀ (a b : ℤ) (hab : a + b = i), HEq (f a b hab) (g a b hab)) :
    HEq (GradedObject.Monoidal.tensorObjDesc f) (GradedObject.Monoidal.tensorObjDesc g) := by
  subst X'
  subst Y'
  subst M'
  have hfg : f = g := by
    funext a b hab
    exact eq_of_heq (h a b hab)
  rw [hfg]

end CochainComplex
