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
# Generic graded and tensor component transports

Componentwise heterogeneous equalities of graded maps assemble into
whole graded-map equality. Native module composition and graded tensor
descent transport those equalities through unchanged carrier equalities.
The complex tensor descent agrees with its original graded construction.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]

/-- Componentwise graded-map transport along the original carrier equalities. -/
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

/-- Tensor complex carriers transport through their original graded tensor objects. -/
theorem tensorObj_X_congr
    {C D C' D' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hC : C.X = C'.X) (hD : D.X = D'.X) :
    (HomologicalComplex.tensorObj C D).X = (HomologicalComplex.tensorObj C' D').X := by
  rw [HomologicalComplex.tensorObj_X_eq_graded, HomologicalComplex.tensorObj_X_eq_graded]
  exact GradedObject.Monoidal.tensorObj_eq C.X D.X C'.X D'.X hC hD

/-- A complex tensor component descends through its original graded tensor object. -/
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

/-- Graded tensor descent transports along the original carriers and component maps. -/
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
