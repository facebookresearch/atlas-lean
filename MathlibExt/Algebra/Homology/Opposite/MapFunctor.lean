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
# Opposite complexes and termwise functor mapping

Let C,D be categories with zero morphisms and F:C→D preserve zero morphisms. The unop functor
sends an object of (HomologicalComplex(Cᵒᵖ,c))ᵒᵖ to a complex in C with reversed shape c.symm.

Unop followed by termwise F is naturally isomorphic to termwise Fᵒᵖ followed by unop. Both
constructions have degree-i coefficient F(unop(K_i)), and the comparison and inverse are
identities in every degree. This uses only the stated zero-morphism assumptions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace HomologicalComplex

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {ι : Type w} (F : C ⥤ D) [F.PreservesZeroMorphisms] (c : ComplexShape ι)

/-- Let C,D be categories with zero morphisms in independent object/morphism universes
(uC,vC),(uD,vD), F:C→D preserve zero morphisms, and c a complex shape on I in w. On objects
K∈(HomologicalComplex(Cᵒᵖ,c))ᵒᵖ, the functors unop_C followed by F on shape c.symm and the
opposite of termwise Fᵒᵖ followed by unop_D are naturally isomorphic. Both have degree-i object
F(unop(K_i)), with identity component maps. -/
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

/-- Let C,D be categories with zero morphisms in independent object/morphism universes
(uC,vC),(uD,vD), F:C→D preserve zero morphisms, and c a complex shape on I in w. For
K∈(HomologicalComplex(Cᵒᵖ,c))ᵒᵖ and i∈I, the degree-i component of the forward comparison
between the two unop/mapping functors is id_{F(unop(K_i))}. -/
@[simp]
theorem unopFunctorCompMapIso_hom_app_f
    (K : (HomologicalComplex Cᵒᵖ c)ᵒᵖ) (i : ι) :
    ((unopFunctorCompMapIso F c).hom.app K).f i = 𝟙 _ := rfl

/-- Let C,D be categories with zero morphisms in independent object/morphism universes
(uC,vC),(uD,vD), F:C→D preserve zero morphisms, and c a complex shape on I in w. For
K∈(HomologicalComplex(Cᵒᵖ,c))ᵒᵖ and i∈I, the inverse comparison has degree-i component
id_{F(unop(K_i))}, with the same reversed shape c.symm. -/
@[simp]
theorem unopFunctorCompMapIso_inv_app_f
    (K : (HomologicalComplex Cᵒᵖ c)ᵒᵖ) (i : ι) :
    ((unopFunctorCompMapIso F c).inv.app K).f i = 𝟙 _ := rfl

end HomologicalComplex
