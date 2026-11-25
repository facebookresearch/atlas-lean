/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ProjectiveRestriction

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uR uS uT vR vS vT

open CategoryTheory

section Restriction

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (F : FGModuleCat.{vR} R ⥤ FGModuleCat.{vS} S)
variable (hP : ∀ P : FGProjectiveCat.{vR} R,
  Module.Projective S (F.obj ((FGProjectiveCat.inclusion R).obj P)))

example (P : FGProjectiveCat.{vR} R) :
    ((FGProjectiveCat.projectiveRestriction F hP).obj P).obj =
      (F.obj ((FGProjectiveCat.inclusion R).obj P)).obj :=
  FGProjectiveCat.projectiveRestriction_obj_obj F hP P

example {P Q : FGProjectiveCat.{vR} R} (f : P ⟶ Q) :
    ((FGProjectiveCat.projectiveRestriction F hP).map f).hom.hom =
      (F.map ((FGProjectiveCat.inclusion R).map f)).hom.hom :=
  FGProjectiveCat.projectiveRestriction_map_hom F hP f

example :
    FGProjectiveCat.projectiveRestriction F hP ⋙ FGProjectiveCat.inclusion S ≅
      FGProjectiveCat.inclusion R ⋙ F :=
  FGProjectiveCat.projectiveRestrictionInclusionIso F hP

variable [F.Additive]

example : (FGProjectiveCat.projectiveRestriction F hP).Additive := inferInstance

example : (FGProjectiveCat.projectiveRestriction F hP).IsExact := inferInstance

end Restriction

section Identity

variable (R : Type uR) [Ring R]

example :
    FGProjectiveCat.projectiveRestriction (𝟭 (FGModuleCat.{vR} R))
        (FGProjectiveCat.identityProjectivePreservation R) ≅
      𝟭 (FGProjectiveCat.{vR} R) :=
  FGProjectiveCat.projectiveRestrictionIdentityIso R

end Identity

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]
variable (F : FGModuleCat.{vR} R ⥤ FGModuleCat.{vS} S)
variable (G : FGModuleCat.{vS} S ⥤ FGModuleCat.{vT} T)
variable (hPF : ∀ P : FGProjectiveCat.{vR} R,
  Module.Projective S (F.obj ((FGProjectiveCat.inclusion R).obj P)))
variable (hPG : ∀ P : FGProjectiveCat.{vS} S,
  Module.Projective T (G.obj ((FGProjectiveCat.inclusion S).obj P)))

example :
    FGProjectiveCat.projectiveRestriction (F ⋙ G)
        (FGProjectiveCat.compositeProjectivePreservation F G hPF hPG) ≅
      FGProjectiveCat.projectiveRestriction F hPF ⋙
        FGProjectiveCat.projectiveRestriction G hPG :=
  FGProjectiveCat.projectiveRestrictionCompositionIso F G hPF hPG

example {P Q : FGProjectiveCat.{vR} R} (f : P ⟶ Q) :
    ((FGProjectiveCat.projectiveRestriction (F ⋙ G)
      (FGProjectiveCat.compositeProjectivePreservation F G hPF hPG)).map f).hom.hom =
        (G.map (F.map ((FGProjectiveCat.inclusion R).map f))).hom.hom :=
  rfl

end Composition

end
