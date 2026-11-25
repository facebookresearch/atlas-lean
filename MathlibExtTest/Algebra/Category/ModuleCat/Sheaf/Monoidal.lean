/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

universe u

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- Instance synthesis for sheaves of modules over a sheaf of commutative rings. -/
example : MonoidalCategory (SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) :=
  inferInstance

example : SymmetricCategory (SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) :=
  inferInstance

example : MonoidalClosed (SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) :=
  inferInstance

example : (SheafOfModules.sheafifyFunctor 𝒪 h𝒪).Monoidal := inferInstance

/-- The monoidal unit is the structure sheaf. -/
example : 𝟙_ (SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) =
    SheafOfModules.unit (SheafOfModules.ringSheaf 𝒪 h𝒪) := rfl

/-- The internal hom of the presheaves underlying two sheaves of modules is a sheaf
(`PresheafOfModules.isSheaf_ihom`), so sheafification leaves it unchanged. -/
example (L M : SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) :
    IsIso ((SheafOfModules.sheafifyAdj 𝒪 h𝒪).unit.app ((ihom L.val).obj M.val)) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.sheafifyAdj 𝒪 h𝒪).unit.app ((ihom L.val).obj M.val))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J (PresheafOfModules.isSheaf_ihom L.val M.val M.isSheaf)
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-- Currying for sheaves of modules. -/
example (L M N : SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)) :
    (L ⊗ M ⟶ N) ≃ (M ⟶ (ihom L).obj N) :=
  (ihom.adjunction L).homEquiv M N

/-- Tensoring a morphism inverted by sheafification with any presheaf of modules gives a morphism
inverted by sheafification. -/
example {P Q : PresheafOfModulesOfCommRing.{u} 𝒪} (g : P ⟶ Q)
    (hg : IsIso ((SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map g))
    (P' : PresheafOfModulesOfCommRing.{u} 𝒪) :
    IsIso ((SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map (g ▷ P')) := by
  have hW : SheafOfModules.presheafW J 𝒪 = (MorphismProperty.isomorphisms _).inverseImage
      (SheafOfModules.sheafifyFunctor 𝒪 h𝒪) :=
    PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (R := SheafOfModules.ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))
  have h := SheafOfModules.presheafW_isMonoidal 𝒪 h𝒪
  rw [hW] at h
  exact h.whiskerRight g hg P'

/-- The comparison of `L ⊗ M` with the sheafified presheaf tensor product is natural. -/
example {L L' M M' : SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)} (f : L ⟶ L')
    (g : M ⟶ M') :
    (SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorIsoSheafify 𝒪 h𝒪 L' M').hom =
      (SheafOfModules.tensorIsoSheafify 𝒪 h𝒪 L M).hom ≫ (f ⊗ₘ g) := by
  have nat {A B : SheafOfModules.{u} (SheafOfModules.ringSheaf 𝒪 h𝒪)} (v : A ⟶ B) :
      (SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map v.val ≫
          (SheafOfModules.sheafifyCounitIso 𝒪 h𝒪 B).hom =
        (SheafOfModules.sheafifyCounitIso 𝒪 h𝒪 A).hom ≫ v :=
    (SheafOfModules.sheafifyAdj 𝒪 h𝒪).counit.naturality v
  simp only [SheafOfModules.tensorIsoSheafify, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, Category.assoc]
  erw [tensorIso_hom, tensorIso_hom]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  erw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, nat f, nat g]
  rfl

end
