/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The additive internal-Hom construction and its identity/composition
proofs adapt Mathlib/CategoryTheory/Sites/SheafHom.lean:
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0; author Joël Riou.
Source revision: 56a005855ea17e0b0958f73ec801ae140b0a1679.
Modification: retain the native abelian-group structure on local Hom
sets and right-derive this actual additive sheaf-valued functor.
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Actual internal Ext sheaves of abelian coefficient sheaves

The degree-zero functor is the abelian-group sheaf of the actual
restriction Hom sets on every slice site. Its right-derived functors
are computed by native injective resolutions. This defines internal
Ext, rather than replacing it by global Ext groups or by a chosen
coefficient module. Both source and target morphisms have their original
precomposition or postcomposition action.

Reference: Stacks Project, Tags 01DH and 070I; Berthelot--Breen--Messing,
*Théorie de Dieudonné cristalline II*, the crystalline Ext realization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafInternalExtModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Actual integral abelian coefficient sheaves, in a universe containing the site. -/
abbrev AbelianSheaves := Sheaf J AddCommGrpCat.{max u v}

variable (F G : AbelianSheaves J)

/-- The local Hom groups of the actual restrictions to each slice site. -/
def homPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj X := AddCommGrpCat.of (F.over X.unop ⟶ G.over X.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := (J.overMapPullback AddCommGrpCat f.unop).map
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_id X) φ
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_comp f g) φ

/-- Internal Hom is a genuine abelian-group sheaf on the original site. -/
def homSheaf : AbelianSheaves J where
  obj := homPresheaf J F G
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{max u v})
    change Presheaf.IsSheaf J (sheafHom' F G)
    exact (sheafHom F G).property

variable {F G} {H : AbelianSheaves J}

/-- Postcomposition by the actual target sheaf map. -/
def postcompose (f : G ⟶ H) : homSheaf J F G ⟶ homSheaf J F H where
  hom.app X := AddCommGrpCat.ofHom
    { toFun (φ : F.over X.unop ⟶ G.over X.unop) :=
        φ ≫ (J.overPullback AddCommGrpCat X.unop).map f
      map_zero' := by exact zero_comp
      map_add' := fun φ ψ ↦ by simp only [Preadditive.add_comp] }
  hom.naturality {X Y} a := by
    apply ConcreteCategory.hom_ext
    intro φ
    dsimp [homSheaf, homPresheaf] at φ ⊢
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl

/-- Precomposition by the actual source sheaf map. -/
def precompose (f : F ⟶ G) : homSheaf J G H ⟶ homSheaf J F H where
  hom.app X := AddCommGrpCat.ofHom
    { toFun (φ : G.over X.unop ⟶ H.over X.unop) :=
        (J.overPullback AddCommGrpCat X.unop).map f ≫ φ
      map_zero' := by exact comp_zero
      map_add' := fun φ ψ ↦ by simp only [Preadditive.comp_add] }
  hom.naturality {X Y} a := by
    apply ConcreteCategory.hom_ext
    intro φ
    dsimp [homSheaf, homPresheaf] at φ ⊢
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl

variable (F)

/-- The actual additive internal-Hom functor in the second variable. -/
def homFunctor : AbelianSheaves J ⥤ AbelianSheaves J where
  obj := homSheaf J F
  map f := postcompose J f
  map_id G := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro φ
    dsimp [homSheaf, homPresheaf] at φ ⊢
    change φ ≫ (J.overPullback AddCommGrpCat X.unop).map (𝟙 G) = φ
    rw [_root_.CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro φ
    dsimp [homSheaf, homPresheaf] at φ ⊢
    change φ ≫ (J.overPullback AddCommGrpCat X.unop).map (f ≫ g) =
      (φ ≫ (J.overPullback AddCommGrpCat X.unop).map f) ≫
        (J.overPullback AddCommGrpCat X.unop).map g
    rw [_root_.CategoryTheory.Functor.map_comp, Category.assoc]

instance homFunctor_additive : (homFunctor J F).Additive where
  map_add {G H f g} := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro φ
    dsimp [homFunctor, postcompose, homSheaf, homPresheaf] at φ ⊢
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [HasInjectiveResolutions (AbelianSheaves J)]

/-- Internal Ext is the native right-derived internal-Hom functor. -/
def internalExtFunctor (n : ℕ) : AbelianSheaves J ⥤ AbelianSheaves J :=
  (homFunctor J F).rightDerived n

/-- The original two coefficient sheaves fix this internal Ext sheaf. -/
def internalExt (G : AbelianSheaves J) (n : ℕ) : AbelianSheaves J :=
  (internalExtFunctor J F n).obj G

/-- Its actual injective-resolution cochains, before taking sheaf homology. -/
def extCochains (G : AbelianSheaves J) : CochainComplex (AbelianSheaves J) ℕ :=
  ((homFunctor J F).mapHomologicalComplex _).obj
    (injectiveResolution G).cocomplex

/-- The native resolution comparison fixes the complete Ext normalization. -/
def internalExtResolutionIso (G : AbelianSheaves J) (n : ℕ) :
    internalExt J F G n ≅ (extCochains J F G).homology n :=
  (injectiveResolution G).isoRightDerivedObj (homFunctor J F) n

end MathlibExt.CategoryTheory.SheafInternalExtModels
