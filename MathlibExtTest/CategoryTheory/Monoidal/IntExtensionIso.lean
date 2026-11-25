/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntExtensionIso
import MathlibExt.CategoryTheory.Monoidal.RelCat
noncomputable section
open CategoryTheory MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  [RightRigidCategory D]
variable (T : SymmetricTrace C) {F G H : C ⥤ D} [F.Braided] [G.Braided] [H.Braided]
  (hF : T.Preserves (symmetricTraceOfRigid D) F)
  (hG : T.Preserves (symmetricTraceOfRigid D) G)
  (hH : T.Preserves (symmetricTraceOfRigid D) H)
  (i : F ≅ G) [NatTrans.IsMonoidal i.hom]
open IntConstruction
example : extend T F hF ≅ extend T G hG := extendIso T hF hG i

example : NatTrans.IsMonoidal (extendIso T hF hG i).hom := inferInstance
example : NatTrans.IsMonoidal (extendIso T hF hG i).inv := inferInstance
example (X : IntConstruction T) : (extend T F hF).obj X ≅ (extend T G hG).obj X :=
  (extendIso T hF hG i).app X
example {X Y : IntConstruction T} (f : X ⟶ Y) :
    (extend T F hF).map f ≫ (extendIso T hF hG i).hom.app Y =
      (extendIso T hF hG i).hom.app X ≫ (extend T G hG).map f :=
  (extendIso T hF hG i).hom.naturality f
example (A : C) :
    (extendIso T hF hG i).hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
      (extensionIso T F hF).hom.app A ≫ i.hom.app A := extensionIso_natural T hF hG i A
example : Functor.isoWhiskerLeft (embedding T) (extendIso T hF hG i) ≪≫ extensionIso T G hG =
    extensionIso T F hF ≪≫ i := extensionIso_natural_iso T hF hG i

-- Component and tensor coherence are available without unfolding the chosen inverse functor.
example (X : IntConstruction T) :
    (extendIso T hF hG i).hom.app X =
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse.map
        (mapPair (symmetricTraceOfRigid D) (i.hom.app X.positive) (i.inv.app X.negative)) :=
  extendIso_hom_app T hF hG i X
example (X Y : IntConstruction T) :
    Functor.LaxMonoidal.μ (extend T F hF) X Y ≫ (extendIso T hF hG i).hom.app (X ⊗ Y) =
      ((extendIso T hF hG i).hom.app X ⊗ₘ (extendIso T hF hG i).hom.app Y) ≫
        Functor.LaxMonoidal.μ (extend T G hG) X Y := NatTrans.IsMonoidal.tensor X Y

-- Laws use independent source/target universes and arbitrary supplied isomorphisms.
local instance : NatTrans.IsMonoidal (Iso.refl F).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))
local instance (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    NatTrans.IsMonoidal (i ≪≫ j).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (i.hom ≫ j.hom))
local instance : NatTrans.IsMonoidal i.symm.hom :=
  inferInstanceAs (NatTrans.IsMonoidal i.inv)
example : extendIso T hF hF (Iso.refl F) = Iso.refl (extend T F hF) := extendIso_refl T hF
example (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    extendIso T hF hH (i ≪≫ j) = extendIso T hF hG i ≪≫ extendIso T hG hH j :=
  extendIso_trans T hF hG i hH j
example : extendIso T hG hF i.symm = (extendIso T hF hG i).symm := extendIso_symm T hF hG i
example (X : IntConstruction T) :
    (extendIso T hF hG i).hom.app X ≫ (extendIso T hF hG i).inv.app X = 𝟙 _ := by simp
example :
    (extendIso T hF hG i).hom.app (𝟙_ (IntConstruction T)) ≫
      (extendIso T hF hG i).inv.app (𝟙_ (IntConstruction T)) = 𝟙 _ := by simp

-- Compatibility determines the whole lift, not just its embedded components.
example (j : extend T F hF ≅ extend T G hG) [NatTrans.IsMonoidal j.hom]
    (h : ∀ A, j.hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
      (extensionIso T F hF).hom.app A ≫ i.hom.app A) : j = extendIso T hF hG i :=
  extendIso_unique T hF hG i j h
example : ∃! j : extend T F hF ≅ extend T G hG, NatTrans.IsMonoidal j.hom ∧
    ∀ A, j.hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
      (extensionIso T F hF).hom.app A ≫ i.hom.app A := existsUnique_extendIso T hF hG i

-- Target recovery in the concrete product-relational model.
private abbrev relTrace := RelCat.symmetricTrace.{0}
private abbrev relPreserves : relTrace.Preserves (symmetricTraceOfRigid RelCat.{0})
    (𝟭 RelCat.{0}) := SymmetricTrace.preserves_of_rigid _
example : extendIso relTrace relPreserves relPreserves (Iso.refl (𝟭 RelCat.{0})) =
    Iso.refl (extend relTrace (𝟭 RelCat.{0}) relPreserves) := extendIso_refl relTrace relPreserves
