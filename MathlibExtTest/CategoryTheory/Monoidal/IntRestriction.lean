/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntRestriction
import MathlibExt.CategoryTheory.Monoidal.RelCat
open CategoryTheory MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C]
variable (T : SymmetricTrace C) (F G : IntConstruction T ⥤ D) [F.Monoidal] [G.Monoidal]
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((IntConstruction.embedding T).obj A) =
      i.hom.app ((IntConstruction.embedding T).obj A)) : e = i :=
  IntConstruction.monoidalIso_ext T e i h

open IntConstruction

-- Restriction equality is sufficient, with independent source/target universes.
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e = Functor.isoWhiskerLeft (embedding T) i) :
    e = i := monoidalIso_eq_of_whiskerLeft_eq T e i h

-- Equality on positives also determines the negative and mixed components.
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((embedding T).obj A) = i.hom.app ((embedding T).obj A)) (A : C) :
    e.hom.app (⟨𝟙_ C,A⟩ : IntConstruction T) = i.hom.app (⟨𝟙_ C,A⟩ : IntConstruction T) := by
  rw [monoidalIso_ext T e i h]
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((embedding T).obj A) = i.hom.app ((embedding T).obj A)) (A U : C) :
    e.inv.app (⟨A,U⟩ : IntConstruction T) = i.inv.app (⟨A,U⟩ : IntConstruction T) := by
  rw [monoidalIso_ext T e i h]
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((embedding T).obj A) = i.hom.app ((embedding T).obj A)) :
    e.hom.app (𝟙_ (IntConstruction T)) = i.hom.app (𝟙_ (IntConstruction T)) := by
  rw [monoidalIso_ext T e i h]

-- An automorphism trivial on the embedding is trivial everywhere.
example (e : F ≅ F) [NatTrans.IsMonoidal e.hom]
    (h : ∀ A, e.hom.app ((embedding T).obj A) = 𝟙 _) : e = Iso.refl F := by
  let _ : NatTrans.IsMonoidal (Iso.refl F).hom := inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))
  exact monoidalIso_ext T e (Iso.refl F) h

-- Both directions of an isomorphism can be used as the restriction data.
example (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.inv.app ((embedding T).obj A) = i.inv.app ((embedding T).obj A)) : e = i := by
  have he : NatTrans.IsMonoidal e.symm.hom := inferInstanceAs (NatTrans.IsMonoidal e.inv)
  have hi : NatTrans.IsMonoidal i.symm.hom := inferInstanceAs (NatTrans.IsMonoidal i.inv)
  have hs := monoidalIso_ext T e.symm i.symm h
  exact congrArg Iso.symm hs

-- A family of prescribed positive components has at most one monoidal lift.
example (a : ∀ A, F.obj ((embedding T).obj A) ⟶ G.obj ((embedding T).obj A))
    (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (he : ∀ A, e.hom.app ((embedding T).obj A) = a A)
    (hi : ∀ A, i.hom.app ((embedding T).obj A) = a A) : e = i :=
  monoidalIso_ext T e i (fun A => (he A).trans (hi A).symm)

-- This specialization uses the product-relational Int model.
example (F G : IntConstruction RelCat.symmetricTrace.{0} ⥤ D) [F.Monoidal] [G.Monoidal]
    (e i : F ≅ G) [NatTrans.IsMonoidal e.hom] [NatTrans.IsMonoidal i.hom]
    (h : ∀ A, e.hom.app ((embedding RelCat.symmetricTrace.{0}).obj A) =
      i.hom.app ((embedding RelCat.symmetricTrace.{0}).obj A)) : e = i :=
  monoidalIso_ext RelCat.symmetricTrace.{0} e i h
