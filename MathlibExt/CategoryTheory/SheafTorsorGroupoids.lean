/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Actual torsor sheaves and their isomorphism groupoids

For a specified native group sheaf, an action is a morphism of actual
sheaves with every unit and associativity law. A torsor is locally
inhabited and its native action-to-pair map is invertible. Its groupoid
is the core of the category of actual equivariant sheaf maps.
No abstract category of torsors is selected.

References: Stacks Project, Tags 04UV and 03AG; Fargues--Scholze,
arXiv:2102.13459v4, Section III.1; Mirkovic--Vilonen,
arXiv:math/0401222v5, Sections 4--5.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.CategoryTheory.SheafTorsorGroupoids

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (G : Sheaf J GrpCat.{w})

/-- The original underlying set sheaf of the actual group sheaf. -/
def groupSets : Sheaf J (Type w) :=
  (sheafCompose J (forget GrpCat.{w})).obj G

instance groupSections (T : Cᵒᵖ) : Group ((groupSets J G).obj.obj T) :=
  inferInstanceAs (Group (G.obj.obj T))

/-- Literal pointwise product of the original presheaf sections. -/
def pairs (A B : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj T := A.obj T × B.obj T
  map f := TypeCat.ofHom (fun x ↦ (A.map f x.1, B.map f x.2))
  map_id T := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- An actual right-action sheaf, including all native sectionwise laws. -/
structure Action where
  sheaf : Sheaf J (Type w)
  action : pairs sheaf.obj (groupSets J G).obj ⟶ sheaf.obj
  unit : ∀ (T : Cᵒᵖ) (x : sheaf.obj.obj T), action.app T (x, 1) = x
  associative : ∀ (T : Cᵒᵖ) (x : sheaf.obj.obj T)
    (g h : (groupSets J G).obj.obj T),
    action.app T (action.app T (x, g), h) = action.app T (x, g * h)

/-- Morphisms retain their actual underlying sheaf map and full equivariance. -/
def ActionHom (X Y : Action J G) :=
  {f : X.sheaf ⟶ Y.sheaf //
    ∀ (T : Cᵒᵖ) (x : X.sheaf.obj.obj T) (g : (groupSets J G).obj.obj T),
      f.hom.app T (X.action.app T (x, g)) =
        Y.action.app T (f.hom.app T x, g)}

instance : Category (Action J G) where
  Hom := ActionHom J G
  id X := ⟨𝟙 X.sheaf, by intros; rfl⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    intro T x h
    change g.val.hom.app T (f.val.hom.app T (X.action.app T (x, h))) =
      Z.action.app T (g.val.hom.app T (f.val.hom.app T x), h)
    rw [f.property, g.property]
    ⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

/-- The actual action category forgets to its displayed native sheaf maps. -/
def forgetAction : Action J G ⥤ Sheaf J (Type w) where
  obj X := X.sheaf
  map {X Y} f := (show ActionHom J G X Y from f).val

instance forgetAction_faithful : (forgetAction J G).Faithful where
  map_injective h := Subtype.ext h

/-- The native right-action comparison (p,g) maps to (p,p*g). -/
def actionPair (X : Action J G) : pairs X.sheaf.obj (groupSets J G).obj ⟶
    pairs X.sheaf.obj X.sheaf.obj where
  app T := TypeCat.ofHom (fun x ↦ (x.1, X.action.app T x))
  naturality T U f := by
    ext x
    exact Prod.ext rfl (congrArg (fun a ↦ a x) (X.action.naturality f))

/-- Local inhabitation and simple transitivity are actual topos conditions. -/
def IsTorsor (X : Action J G) : Prop :=
  Epi (terminal.from X.sheaf) ∧ IsIso (actionPair J G X)

/-- Actual torsors form the core of their full equivariant action subcategory. -/
abbrev TorsorGroupoid :=
  Core (show ObjectProperty (Action J G) from IsTorsor J G).FullSubcategory

end MathlibExt.CategoryTheory.SheafTorsorGroupoids
