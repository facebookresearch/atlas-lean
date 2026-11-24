/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Restriction

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex

universe uC vC uD vD w₁ w₂

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {ι₁ : Type w₁} {ι₂ : Type w₂} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  (e : c₁.Embedding c₂) [e.IsRelIff] (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Native restriction commutes with a mapped complex using its original coefficients. -/
def restrictionFunctorCompMapIso :
    e.restrictionFunctor C ⋙ F.mapHomologicalComplex c₁ ≅
      F.mapHomologicalComplex c₂ ⋙ e.restrictionFunctor D :=
  NatIso.ofComponents
    (fun K => Hom.isoOfComponents
      (fun i => (Iso.refl (F.obj (K.X (e.f i))) :
        ((e.restrictionFunctor C ⋙ F.mapHomologicalComplex c₁).obj K).X i ≅
          ((F.mapHomologicalComplex c₂ ⋙ e.restrictionFunctor D).obj K).X i))
      (by
        intro i j hij
        change (𝟙 (F.obj (K.X (e.f i)))) ≫ F.map (K.d (e.f i) (e.f j)) =
          F.map (K.d (e.f i) (e.f j)) ≫ (𝟙 (F.obj (K.X (e.f j))))
        rw [Category.id_comp, Category.comp_id]))
    (by
      intro K L f
      apply HomologicalComplex.hom_ext
      intro i
      change F.map (f.f (e.f i)) ≫ (𝟙 (F.obj (L.X (e.f i)))) =
        (𝟙 (F.obj (K.X (e.f i)))) ≫ F.map (f.f (e.f i))
      rw [Category.comp_id, Category.id_comp])

/-- The restriction comparison keeps the original coefficient maps in every degree. -/
@[simp]
theorem restrictionFunctorCompMapIso_hom_app_f (K : HomologicalComplex C c₂) (i : ι₁) :
    ((restrictionFunctorCompMapIso e F).hom.app K).f i = 𝟙 _ := rfl

end HomologicalComplex
