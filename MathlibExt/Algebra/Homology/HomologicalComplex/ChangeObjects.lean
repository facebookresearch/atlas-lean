/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Changing the objects of a homological complex

A family of object isomorphisms transports every original differential to
its specified coordinates. The native component constructor assembles the
resulting complex isomorphism. The construction uses only zero morphisms
and applies to arbitrary complex shapes and independent index universes.
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Category Limits

universe u v w

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) {X : ι → C}

/-- Replace every object by its specified coordinates and conjugate the original differential. -/
def changeObjects (e : ∀ i, K.X i ≅ X i) : HomologicalComplex C c where
  X := X
  d i j := (e i).inv ≫ K.d i j ≫ (e j).hom
  shape i j h := by
    simp only [K.shape i j h, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (K.d i j) (K.d j k) (e k).hom, K.d_comp_d,
      zero_comp, comp_zero]

/-- Each transported degree has the specified original target object. -/
@[simp]
lemma changeObjects_X (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjects e).X i = X i := rfl

/-- The transported differential is the actual conjugate of the original differential. -/
@[simp]
lemma changeObjects_d (e : ∀ i, K.X i ≅ X i) (i j : ι) :
    (K.changeObjects e).d i j = (e i).inv ≫ K.d i j ≫ (e j).hom := rfl

/-- The native component constructor identifies the complex with its specified coordinates. -/
def changeObjectsIso (e : ∀ i, K.X i ≅ X i) : K ≅ K.changeObjects e :=
  Hom.isoOfComponents e (by
    intro i j _
    change (e i).hom ≫ (e i).inv ≫ K.d i j ≫ (e j).hom = K.d i j ≫ (e j).hom
    exact (e i).hom_inv_id_assoc (K.d i j ≫ (e j).hom))

/-- The forward comparison has exactly the specified degreewise coordinate map. -/
@[simp]
lemma changeObjectsIso_hom_f (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjectsIso e).hom.f i = (e i).hom := rfl

/-- The inverse comparison restores the original object coordinates in each degree. -/
@[simp]
lemma changeObjectsIso_inv_f (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjectsIso e).inv.f i = (e i).inv := rfl

variable {K} {L M : HomologicalComplex C c} {Y Z : ι → C}

/-- An original complex morphism acts on both families of actual object coordinates. -/
def changeObjectsMap (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) :
    K.changeObjects e ⟶ L.changeObjects f :=
  (K.changeObjectsIso e).inv ≫ φ ≫ (L.changeObjectsIso f).hom

/-- Each map component is the original component conjugated by its two object maps. -/
@[simp]
lemma changeObjectsMap_f (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) (i : ι) :
    (changeObjectsMap φ e f).f i = (e i).inv ≫ φ.f i ≫ (f i).hom := rfl

/-- The forward object comparison is natural for every original complex morphism. -/
@[reassoc]
lemma changeObjectsIso_hom_naturality (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) :
    φ ≫ (L.changeObjectsIso f).hom =
      (K.changeObjectsIso e).hom ≫ changeObjectsMap φ e f := by
  simp only [changeObjectsMap, Iso.hom_inv_id_assoc]

/-- Identity acts identically after the specified coordinate change. -/
@[simp]
lemma changeObjectsMap_id (e : ∀ i, K.X i ≅ X i) :
    changeObjectsMap (𝟙 K) e e = 𝟙 (K.changeObjects e) := by
  simp only [changeObjectsMap, Category.id_comp, Iso.inv_hom_id]

/-- Coordinate changes preserve composition of the original complex morphisms. -/
lemma changeObjectsMap_comp (φ : K ⟶ L) (ψ : L ⟶ M)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) (g : ∀ i, M.X i ≅ Z i) :
    changeObjectsMap (φ ≫ ψ) e g = changeObjectsMap φ e f ≫ changeObjectsMap ψ f g := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id_assoc]

section Functor

universe u' v'

variable {D : Type u'} [Category.{v'} D]
  (F : D ⥤ HomologicalComplex C c) (Y' : D → ι → C)
  (e : ∀ A i, (F.obj A).X i ≅ Y' A i)

/-- Present the values of a complex-valued functor in specified object coordinates. -/
def changeObjectsFunctor : D ⥤ HomologicalComplex C c where
  obj A := (F.obj A).changeObjects (e A)
  map f := changeObjectsMap (F.map f) (e _) (e _)
  map_id A := by
    rw [F.map_id, changeObjectsMap_id]
  map_comp f g := by
    rw [F.map_comp]
    exact changeObjectsMap_comp (F.map f) (F.map g) (e _) (e _) (e _)

/-- The original functor and its object-coordinate presentation are naturally isomorphic. -/
def changeObjectsFunctorIso : F ≅ changeObjectsFunctor F Y' e :=
  NatIso.ofComponents (fun A => (F.obj A).changeObjectsIso (e A))
    (fun f => changeObjectsIso_hom_naturality (F.map f) (e _) (e _))

end Functor

end HomologicalComplex
