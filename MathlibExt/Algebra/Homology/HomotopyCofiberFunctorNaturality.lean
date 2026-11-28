/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomotopyCofiber

/-!
# Naturality of the additive-functor cofiber comparison

Let H:C → D be additive between preadditive categories with binary
biproducts. Let c have decidable differential relation and suppose every
degree has a predecessor. The inverse comparison
ε_φ⁻¹:Cofib(H(φ)) → H(Cofib(φ)) is natural in commuting squares
between complex morphisms φ and ψ.

The cofiber map of the square after applying H, followed by ε_ψ⁻¹,
equals ε_φ⁻¹ followed by H applied to the cofiber map of the original
square. The category and index universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD w

namespace HomologicalComplex.homotopyCofiber

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  (H : C ⥤ D) [H.Additive] (hc : ∀ j, ∃ i, c.Rel i j)

/-- Let H:C → D be additive between preadditive categories with binary
biproducts, and let c have decidable differential relation and a
predecessor in every degree. For a commuting square a from
φ:F → G to ψ:F′ → G′, write M(a) for its induced cofiber map
and ε_φ:H(Cofib(φ)) ≅ Cofib(H(φ)) for the canonical comparison.
Then ε_ψ⁻¹ ∘ M(H(a)) = H(M(a)) ∘ ε_φ⁻¹. -/
@[reassoc]
theorem mapHomologicalComplexObjIso_inv_naturality
    {F G F' G' : HomologicalComplex C c} {φ : F ⟶ G} {ψ : F' ⟶ G'}
    (a : Arrow.mk φ ⟶ Arrow.mk ψ) :
    mapArrowHom ((H.mapHomologicalComplex c).map φ) ((H.mapHomologicalComplex c).map ψ) hc
        ((H.mapHomologicalComplex c).mapArrow.map a) ≫ (mapHomologicalComplexObjIso ψ H).inv =
      (mapHomologicalComplexObjIso φ H).inv ≫
        (H.mapHomologicalComplex c).map (mapArrowHom φ ψ hc a) := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X ((H.mapHomologicalComplex c).map φ) (c.next j) j hj
    · simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [inlX_mapArrowHom_assoc]
      change H.map (a.left.f (c.next j)) ≫
          inlX ((H.mapHomologicalComplex c).map ψ) (c.next j) j hj ≫
            (mapHomologicalComplexObjXIso ψ H j).inv =
        inlX ((H.mapHomologicalComplex c).map φ) (c.next j) j hj ≫
          (mapHomologicalComplexObjXIso φ H j).inv ≫ H.map ((mapArrowHom φ ψ hc a).f j)
      rw [inlX_mapHomologicalComplexObjXIso_inv,
        inlX_mapHomologicalComplexObjXIso_inv_assoc]
      exact (H.map_comp _ _).symm.trans
        ((congrArg H.map (inlX_mapArrowHom hc a (c.next j) j hj).symm).trans (H.map_comp _ _))
    · simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [inrX_mapArrowHom_assoc]
      change H.map (a.right.f j) ≫ inrX ((H.mapHomologicalComplex c).map ψ) j ≫
          (mapHomologicalComplexObjXIso ψ H j).inv =
        inrX ((H.mapHomologicalComplex c).map φ) j ≫ (mapHomologicalComplexObjXIso φ H j).inv ≫
          H.map ((mapArrowHom φ ψ hc a).f j)
      rw [inrX_mapHomologicalComplexObjXIso_inv,
        inrX_mapHomologicalComplexObjXIso_inv_assoc]
      exact (H.map_comp _ _).symm.trans
        ((congrArg H.map (inrX_mapArrowHom hc a j).symm).trans (H.map_comp _ _))
  · apply ext_from_X' ((H.mapHomologicalComplex c).map φ) j hj
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [inrX_mapArrowHom_assoc]
    change H.map (a.right.f j) ≫ inrX ((H.mapHomologicalComplex c).map ψ) j ≫
        (mapHomologicalComplexObjXIso ψ H j).inv =
      inrX ((H.mapHomologicalComplex c).map φ) j ≫ (mapHomologicalComplexObjXIso φ H j).inv ≫
        H.map ((mapArrowHom φ ψ hc a).f j)
    rw [inrX_mapHomologicalComplexObjXIso_inv,
      inrX_mapHomologicalComplexObjXIso_inv_assoc]
    exact (H.map_comp _ _).symm.trans
      ((congrArg H.map (inrX_mapArrowHom hc a j).symm).trans (H.map_comp _ _))

end HomologicalComplex.homotopyCofiber

end
