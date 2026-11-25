/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Inclusion
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import Mathlib.CategoryTheory.NatIso

/-!
# Restriction of finite-module functors to finite projectives

The projective restriction retains the original module functor's objects
and linear maps. Additivity comes from the original additive functor;
exactness uses the canonical split structures on the projective categories.
The identity and composition isomorphisms have identity components on the
same original module images. Ring and module universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uR uS uT vR vS vT

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace FGProjectiveCat

section ProjectiveRestriction

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (F : FGModuleCat.{vR} R ⥤ FGModuleCat.{vS} S)
variable (hP : ∀ P : FGProjectiveCat.{vR} R,
  Module.Projective S (F.obj ((inclusion R).obj P)))

/-- The actual restriction of the original module functor to the
original projective categories, using the same modules and linear maps. -/
def projectiveRestriction : FGProjectiveCat.{vR} R ⥤ FGProjectiveCat.{vS} S where
  obj P := by
    let _ : Module.Projective S (F.obj ((inclusion R).obj P)) := hP P
    exact FGProjectiveCat.of (R := S) (F.obj ((inclusion R).obj P))
  map {P Q} f := by
    let _ : Module.Projective S (F.obj ((inclusion R).obj P)) := hP P
    let _ : Module.Projective S (F.obj ((inclusion R).obj Q)) := hP Q
    exact FGProjectiveCat.ofHom (R := S) (F.map ((inclusion R).map f)).hom.hom
  map_id P := by
    apply FGProjectiveCat.hom_ext
    change (F.map ((inclusion R).map (𝟙 P))).hom.hom = LinearMap.id
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply FGProjectiveCat.hom_ext
    change (F.map ((inclusion R).map (f ≫ g))).hom.hom =
      (F.map ((inclusion R).map g)).hom.hom.comp (F.map ((inclusion R).map f)).hom.hom
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The complete underlying module image of the projective restriction
is the original image under the original module functor. -/
theorem projectiveRestriction_obj_obj (P : FGProjectiveCat.{vR} R) :
    ((projectiveRestriction F hP).obj P).obj = (F.obj ((inclusion R).obj P)).obj :=
  rfl

/-- The complete linear map image is the same original mapped linear map. -/
theorem projectiveRestriction_map_hom {P Q : FGProjectiveCat.{vR} R} (f : P ⟶ Q) :
    ((projectiveRestriction F hP).map f).hom.hom =
      (F.map ((inclusion R).map f)).hom.hom :=
  rfl

/-- The actual projective inclusion square has identity components on
the original module images and literal original mapped morphisms. -/
def projectiveRestrictionInclusionIso :
    projectiveRestriction F hP ⋙ inclusion S ≅ inclusion R ⋙ F :=
  NatIso.ofComponents (fun P => Iso.refl (F.obj ((inclusion R).obj P))) (by
    intro P Q f
    rfl)

variable [F.Additive]

/-- Additivity of the actual projective restriction follows from
additivity of the original functor on its actual linear maps. -/
instance projectiveRestrictionAdditive : (projectiveRestriction F hP).Additive where
  map_add {P Q} {f g} := by
    apply (inclusion S).map_injective
    apply FGModuleCat.hom_ext
    change (F.map ((inclusion R).map (f + g))).hom.hom =
      (F.map ((inclusion R).map f)).hom.hom + (F.map ((inclusion R).map g)).hom.hom
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]
    rfl

/-- The actual restriction is exact for the canonical split structures
on the original projective categories. -/
instance projectiveRestriction_exact :
    (projectiveRestriction F hP).IsExact :=
  ExactCategory.isExact_splitSource (projectiveRestriction F hP)

end ProjectiveRestriction

section Identity

variable (R : Type uR) [Ring R]

/-- The identity finite-module functor preserves each actual original
projective inclusion object. -/
theorem identityProjectivePreservation :
    ∀ P : FGProjectiveCat.{vR} R,
      Module.Projective R ((𝟭 (FGModuleCat.{vR} R)).obj ((inclusion R).obj P)) :=
  fun P => P.property.2

/-- Restricting the actual identity functor is the actual projective
identity functor, through identity module components. -/
def projectiveRestrictionIdentityIso :
    projectiveRestriction (𝟭 (FGModuleCat.{vR} R)) (identityProjectivePreservation R) ≅
      𝟭 (FGProjectiveCat.{vR} R) :=
  NatIso.ofComponents (fun P => Iso.refl P) (by intro P Q f; rfl)

end Identity

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]
variable (F : FGModuleCat.{vR} R ⥤ FGModuleCat.{vS} S)
variable (G : FGModuleCat.{vS} S ⥤ FGModuleCat.{vT} T)
variable (hPF : ∀ P : FGProjectiveCat.{vR} R,
  Module.Projective S (F.obj ((inclusion R).obj P)))
variable (hPG : ∀ P : FGProjectiveCat.{vS} S,
  Module.Projective T (G.obj ((inclusion S).obj P)))

include hPF hPG in
/-- The composite module functor preserves projectives by using the
actual original projective image supplied by the first restriction. -/
theorem compositeProjectivePreservation :
    ∀ P : FGProjectiveCat.{vR} R,
      Module.Projective T ((F ⋙ G).obj ((inclusion R).obj P)) := by
  intro P
  have h := hPG ((projectiveRestriction F hPF).obj P)
  change Module.Projective T (G.obj (F.obj ((inclusion R).obj P))) at h
  exact h

/-- The actual restriction of a composite is naturally isomorphic to
the composite of the two actual restrictions, on the same original modules. -/
def projectiveRestrictionCompositionIso :
    projectiveRestriction (F ⋙ G) (compositeProjectivePreservation F G hPF hPG) ≅
      projectiveRestriction F hPF ⋙ projectiveRestriction G hPG :=
  NatIso.ofComponents
    (fun P => Iso.refl ((projectiveRestriction G hPG).obj
      ((projectiveRestriction F hPF).obj P)))
    (by intro P Q f; rfl)

end Composition

end FGProjectiveCat

end
