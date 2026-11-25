/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexMap
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transporting bicomplex models through totalization and homology

Natural isomorphisms between functorial bicomplex models induce natural
isomorphisms of their totals and fixed-degree homology. Additive coefficient
functors preserving the total fibers commute with totalization through the
canonical `mapTotalNatIso` comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₀ w₁ w₂ w₁₂ v₀ u₀ v u v' u'

namespace HomologicalComplex₂

section Model

variable {E : Type u₀} [Category.{v₀} E]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) C]

/-- Totalize a natural isomorphism between functorial bicomplex models. -/
noncomputable def totalNatIsoOfNatIso
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) :
    F ⋙ totalFunctor C c₁ c₂ c₁₂ ≅ G ⋙ totalFunctor C c₁ c₂ c₁₂ :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (totalFunctor C c₁ c₂ c₁₂)).mapIso e

@[simp]
theorem totalNatIsoOfNatIso_refl
    (F : E ⥤ HomologicalComplex₂ C c₁ c₂) :
    totalNatIsoOfNatIso c₁₂ (Iso.refl F) = Iso.refl _ :=
  CategoryTheory.Functor.mapIso_refl _ _

@[simp]
theorem totalNatIsoOfNatIso_symm
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) :
    totalNatIsoOfNatIso c₁₂ e.symm = (totalNatIsoOfNatIso c₁₂ e).symm :=
  CategoryTheory.Functor.mapIso_symm _ _

@[simp]
theorem totalNatIsoOfNatIso_trans
    {F G H : E ⥤ HomologicalComplex₂ C c₁ c₂}
    (e : F ≅ G) (e' : G ≅ H) :
    totalNatIsoOfNatIso c₁₂ (e.trans e') =
      (totalNatIsoOfNatIso c₁₂ e).trans (totalNatIsoOfNatIso c₁₂ e') :=
  CategoryTheory.Functor.mapIso_trans _ _ _


end Model

section ModelHomology

variable {E : Type u₀} [Category.{v₀} E]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) C]

/-- Pass a totalized model isomorphism to fixed-degree homology. -/
noncomputable def homologyNatIsoOfNatIso
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G)
    (n : I₁₂) :
    F ⋙ totalFunctor C c₁ c₂ c₁₂ ⋙
        HomologicalComplex.homologyFunctor C c₁₂ n ≅
      G ⋙ totalFunctor C c₁ c₂ c₁₂ ⋙
        HomologicalComplex.homologyFunctor C c₁₂ n :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (HomologicalComplex.homologyFunctor C c₁₂ n)).mapIso
      (totalNatIsoOfNatIso c₁₂ e)

@[simp]
theorem homologyNatIsoOfNatIso_refl
    (F : E ⥤ HomologicalComplex₂ C c₁ c₂) (n : I₁₂) :
    homologyNatIsoOfNatIso c₁₂ (Iso.refl F) n = Iso.refl _ := by
  rw [homologyNatIsoOfNatIso, totalNatIsoOfNatIso_refl]
  exact CategoryTheory.Functor.mapIso_refl _ _

@[simp]
theorem homologyNatIsoOfNatIso_symm
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂}
    (e : F ≅ G) (n : I₁₂) :
    homologyNatIsoOfNatIso c₁₂ e.symm n =
      (homologyNatIsoOfNatIso c₁₂ e n).symm := by
  rw [homologyNatIsoOfNatIso, totalNatIsoOfNatIso_symm,
    CategoryTheory.Functor.mapIso_symm]
  rfl

@[simp]
theorem homologyNatIsoOfNatIso_trans
    {F G H : E ⥤ HomologicalComplex₂ C c₁ c₂}
    (e : F ≅ G) (e' : G ≅ H) (n : I₁₂) :
    homologyNatIsoOfNatIso c₁₂ (e.trans e') n =
      (homologyNatIsoOfNatIso c₁₂ e n).trans
        (homologyNatIsoOfNatIso c₁₂ e' n) := by
  rw [homologyNatIsoOfNatIso, totalNatIsoOfNatIso_trans,
    CategoryTheory.Functor.mapIso_trans]
  rfl

end ModelHomology


section Coefficients

variable {E : Type u₀} [Category.{v₀} E]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) C]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) D]
  [∀ i₁₂, PreservesColimitsOfShape
    (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) Φ]

/-- A coefficient functor preserving total fibers commutes with totalization,
naturally over any functorial bicomplex model. -/
noncomputable def mapTotalModelNatIso
    (M : E ⥤ HomologicalComplex₂ C c₁ c₂) :
    M ⋙ mapAfterTotalFunctor Φ c₁₂ ≅
      M ⋙ totalAfterMapFunctor Φ c₁₂ :=
  ((CategoryTheory.Functor.whiskeringLeft E _ _).obj M).mapIso
    (mapTotalNatIso Φ c₁₂)

/-- Apply the coefficient functor after totalizing an isomorphism of models.

This is the source-neutral transport used before comparing with
evaluation-before-totalization. -/
noncomputable def mapAfterTotalNatIsoOfNatIso
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) :
    F ⋙ mapAfterTotalFunctor Φ c₁₂ ≅
      G ⋙ mapAfterTotalFunctor Φ c₁₂ :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (Φ.mapHomologicalComplex c₁₂)).mapIso
      (totalNatIsoOfNatIso c₁₂ e)

/-- Transport a bicomplex-model isomorphism after applying coefficients and
totalizing. -/
noncomputable def mapTotalTransportNatIso
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) :
    F ⋙ totalAfterMapFunctor Φ c₁₂ ≅
      G ⋙ totalAfterMapFunctor Φ c₁₂ :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (totalAfterMapFunctor Φ c₁₂)).mapIso e

/-- Transporting through totalization in the source category and conjugating
by the map-total comparison agrees with direct transport after applying
coefficients. -/
theorem mapTotalTransportNatIso_conjugation
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) :
    (mapTotalModelNatIso Φ c₁₂ F).symm.trans
      ((mapAfterTotalNatIsoOfNatIso Φ c₁₂ e).trans
        (mapTotalModelNatIso Φ c₁₂ G)) =
      mapTotalTransportNatIso Φ c₁₂ e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (mapTotalNatIso Φ c₁₂).inv.app (F.obj X) ≫
      ((mapAfterTotalFunctor Φ c₁₂).map (e.hom.app X) ≫
        (mapTotalNatIso Φ c₁₂).hom.app (G.obj X)) =
    (totalAfterMapFunctor Φ c₁₂).map (e.hom.app X)
  rw [(mapTotalNatIso Φ c₁₂).hom.naturality (e.hom.app X)]
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Coefficients

section CoefficientHomology

variable {E : Type u₀} [Category.{v₀} E]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (Φ : C ⥤ D) [Φ.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) C]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) D]
  [∀ i₁₂, PreservesColimitsOfShape
    (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) Φ]

/-- Fixed-degree homology form of `mapTotalModelNatIso`. -/
noncomputable def mapTotalModelHomologyNatIso
    (M : E ⥤ HomologicalComplex₂ C c₁ c₂) (n : I₁₂) :
    M ⋙ mapAfterTotalFunctor Φ c₁₂ ⋙
        HomologicalComplex.homologyFunctor D c₁₂ n ≅
      M ⋙ totalAfterMapFunctor Φ c₁₂ ⋙
        HomologicalComplex.homologyFunctor D c₁₂ n :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (HomologicalComplex.homologyFunctor D c₁₂ n)).mapIso
      (mapTotalModelNatIso Φ c₁₂ M)

/-- Fixed-degree homology of the canonical coefficient-and-total transport
of an isomorphism of bicomplex models. -/
noncomputable def mapTotalTransportHomologyNatIso
    {F G : E ⥤ HomologicalComplex₂ C c₁ c₂} (e : F ≅ G) (n : I₁₂) :
    F ⋙ totalAfterMapFunctor Φ c₁₂ ⋙
        HomologicalComplex.homologyFunctor D c₁₂ n ≅
      G ⋙ totalAfterMapFunctor Φ c₁₂ ⋙
        HomologicalComplex.homologyFunctor D c₁₂ n :=
  ((CategoryTheory.Functor.whiskeringRight E _ _).obj
    (HomologicalComplex.homologyFunctor D c₁₂ n)).mapIso
      (mapTotalTransportNatIso Φ c₁₂ e)

end CoefficientHomology


end HomologicalComplex₂
