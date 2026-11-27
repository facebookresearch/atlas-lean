/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotientNaturality

/-! # Tests for naturality of nested-image biproduct quotients -/

@[expose] public section

open CategoryTheory Limits ZeroObject

noncomputable section

universe v u

namespace CategoryTheory.ImageQuotientNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A X B T A' X' B' T' : C}
variable (a : A ⟶ B) (x : X ⟶ B) (b : B ⟶ T)
variable (a' : A' ⟶ B') (x' : X' ⟶ B') (b' : B' ⟶ T')
variable (α : A ⟶ A') (χ : X ⟶ X') (β : B ⟶ B') (τ : T ⟶ T')
variable (ha : a ≫ β = α ≫ a') (hx : x ≫ β = χ ≫ x')
variable (hb : b ≫ τ = β ≫ b')

#check imageCompMap_naturality
#check biprodQuotientMap
#check cokernel_π_biprodQuotientMap
#check imageQuotientMap
#check cokernel_π_imageQuotientMap
#check imageQuotientBiprodIso_naturality

example :
    cokernel.π (biprod.desc a x) ≫
        biprodQuotientMap a x a' x' α χ β ha hx =
      β ≫ cokernel.π (biprod.desc a' x') :=
  cokernel_π_biprodQuotientMap a x a' x' α χ β ha hx

example :
    cokernel.π (imageCompMap a b) ≫
        imageQuotientMap a b a' b' α β τ ha hb =
      image.map (Arrow.homMk' β τ hb.symm) ≫
        cokernel.π (imageCompMap a' b') :=
  cokernel_π_imageQuotientMap a b a' b' α β τ ha hb

example (hxb : x ≫ b = 0) (hxb' : x' ≫ b' = 0)
    (hS : (ShortComplex.mk x b hxb).Exact)
    (hS' : (ShortComplex.mk x' b' hxb').Exact) :
    biprodQuotientMap a x a' x' α χ β ha hx ≫
        (imageQuotientBiprodIso a' x' b' hxb' hS').hom =
      (imageQuotientBiprodIso a x b hxb hS).hom ≫
        imageQuotientMap a b a' b' α β τ ha hb :=
  imageQuotientBiprodIso_naturality
    a x b a' x' b' α χ β τ ha hx hb hxb hxb' hS hS'

-- Identity vertical maps on an identical diagram.
example (hxb : x ≫ b = 0)
    (hS : (ShortComplex.mk x b hxb).Exact) :
    biprodQuotientMap a x a x (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫
        (imageQuotientBiprodIso a x b hxb hS).hom =
      (imageQuotientBiprodIso a x b hxb hS).hom ≫
        imageQuotientMap a b a b (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp) :=
  imageQuotientBiprodIso_naturality a x b a x b
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simp) (by simp) (by simp) hxb hxb hS hS

-- Proof-irrelevant zero and exactness witnesses.
example (hxb₁ hxb₂ : x ≫ b = 0)
    (hS₁ : (ShortComplex.mk x b hxb₁).Exact)
    (hS₂ : (ShortComplex.mk x b hxb₂).Exact) :
    biprodQuotientMap a x a x (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫
        (imageQuotientBiprodIso a x b hxb₂ hS₂).hom =
      (imageQuotientBiprodIso a x b hxb₁ hS₁).hom ≫
        imageQuotientMap a b a b (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp) :=
  imageQuotientBiprodIso_naturality a x b a x b
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simp) (by simp) (by simp) hxb₁ hxb₂ hS₁ hS₂

-- Isomorphic vertical maps induce isomorphisms on the biproduct quotient.
example [IsIso α] [IsIso χ] [IsIso β] :
    IsIso (biprodQuotientMap a x a' x' α χ β ha hx) := by
  dsimp only [biprodQuotientMap]
  infer_instance

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

-- All-zero data in the concrete zero abelian category.
noncomputable example :
    cokernel (biprod.desc
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)) ⟶
      cokernel (biprod.desc
        (0 : (0 : ZeroModuleCat) ⟶ 0)
        (0 : (0 : ZeroModuleCat) ⟶ 0)) :=
  biprodQuotientMap
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (0 : (0 : ZeroModuleCat) ⟶ 0)
      (by simp) (by simp)

#print axioms imageCompMap_naturality
#print axioms biprodQuotientMap
#print axioms cokernel_π_biprodQuotientMap
#print axioms imageQuotientMap
#print axioms cokernel_π_imageQuotientMap
#print axioms imageQuotientBiprodIso_naturality

end CategoryTheory.ImageQuotientNaturalityTests

end
