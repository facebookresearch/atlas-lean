/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.CategoryTheory.Functor.Opposite

/-!
# Mapping an opposite complex through a functor

The native unop complex and mapHomologicalComplex commute by the actual
identity maps on every coefficient. Only zero morphisms and their preservation
are needed; no additivity, homology or global limit assumption is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace HomologicalComplex

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {ι : Type w} (F : C ⥤ D) [F.PreservesZeroMorphisms] (c : ComplexShape ι)

/-- Native unop commutes with the mapped complex through the original coefficient maps. -/
def unopFunctorCompMapIso :
    unopFunctor C c ⋙ F.mapHomologicalComplex c.symm ≅
      ((F.op).mapHomologicalComplex c).op ⋙ unopFunctor D c :=
  NatIso.ofComponents
    (fun K => Hom.isoOfComponents (fun _ => Iso.refl _) (by
      intro i j hij
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl))
    (by
      intro K L f
      apply Hom.ext
      funext i
      change F.map ((f.unop.f i).unop) ≫ 𝟙 _ =
        𝟙 _ ≫ F.map ((f.unop.f i).unop)
      rw [Category.comp_id, Category.id_comp])

/-- The comparison retains the actual coefficient object in every degree. -/
@[simp]
theorem unopFunctorCompMapIso_hom_app_f
    (K : (HomologicalComplex Cᵒᵖ c)ᵒᵖ) (i : ι) :
    ((unopFunctorCompMapIso F c).hom.app K).f i = 𝟙 _ := rfl

/-- The inverse comparison likewise uses identity coefficient maps. -/
@[simp]
theorem unopFunctorCompMapIso_inv_app_f
    (K : (HomologicalComplex Cᵒᵖ c)ᵒᵖ) (i : ι) :
    ((unopFunctorCompMapIso F c).inv.app K).f i = 𝟙 _ := rfl

end HomologicalComplex
