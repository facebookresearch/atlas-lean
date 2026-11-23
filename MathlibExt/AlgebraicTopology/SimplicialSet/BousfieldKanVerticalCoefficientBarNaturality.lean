/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalCoefficientBar

/-!
# Naturality of the Bousfield--Kan vertical coefficient bar

The comparison from the horizontal complex of Bousfield--Kan vertical
homology to the coefficient-bar complex is natural in the simplicial-set
valued diagram.  The source map is supplied directly by the functor defining
`verticalHomologyComplex`; the target map is the alternating complex map
induced by `coefficientBarSimplicialMap`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe w vJ

namespace SSet

variable {J : Type w} [Category.{vJ} J]

local notation "c" => ComplexShape.down ℕ

private theorem bkAlternatingVerticalHomologyIso_hom_naturality
    (R : AddCommGrpCat.{max w vJ}) {D E : J ⥤ SSet.{max w vJ}}
    (α : D ⟶ E) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (((bkAlternatingBicomplexFunctor AddCommGrpCat.{max w vJ} R).map α).f p) q ≫
        (bkAlternatingVerticalHomologyIso R E p q).hom =
      (bkAlternatingVerticalHomologyIso R D p q).hom ≫
        StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) p
            (Functor.whiskerRight α (SSet.homologyFunctor R q)) := by
  change SSet.homologyMap
        (StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) p α) R q ≫
      (homologySigmaIso
        (fun x : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) p ↦ E.obj x.1.left) R q).hom =
    (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) p ↦ D.obj x.1.left) R q).hom ≫
      StrictOrdinaryWeightedBar.wbarMapF
        (W := CategoryBar.replUnit J) p
          (Functor.whiskerRight α (SSet.homologyFunctor R q))
  exact homologySigmaIso_naturality
    (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) p ↦ x)
    (fun x ↦ α.app x.1.left) R q

private theorem terminalWeightCoefficientBarDegreeIso_hom_naturality
    {M N : J ⥤ AddCommGrpCat.{max w vJ}} (α : M ⟶ N) (p : ℕ) :
    StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) p α ≫
        (CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          N p).hom =
      (CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          M p).hom ≫
        CategoryTheory.CategoryHomology.coefficientBarMap α p := by
  apply Sigma.hom_ext
  intro x
  change StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) M p x ≫
      (StrictOrdinaryWeightedBar.wbarMapF
          (W := CategoryBar.replUnit J) p α ≫
        (CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          N p).hom) =
    StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) M p x ≫
      ((CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          M p).hom ≫
        CategoryTheory.CategoryHomology.coefficientBarMap α p)
  rw [← Category.assoc, StrictOrdinaryWeightedBar.wbarMapF_ι,
    Category.assoc,
    CategoryTheory.CategoryHomology.wbarIncl_terminalWeightCoefficientBarDegreeIso_hom,
    ← Category.assoc,
    CategoryTheory.CategoryHomology.wbarIncl_terminalWeightCoefficientBarDegreeIso_hom,
    CategoryTheory.CategoryHomology.coefficientBarι_map]

/-- The Bousfield--Kan vertical-homology/coefficient-bar comparison is
natural in the simplicial-set valued diagram. -/
theorem bkVerticalHomologyCoefficientBarComplexIso_hom_naturality
    (R : AddCommGrpCat.{max w vJ}) {D E : J ⥤ SSet.{max w vJ}}
    (α : D ⟶ E) (q : ℕ) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max w vJ} c q).mapHomologicalComplex c).map
          ((bkAlternatingBicomplexFunctor AddCommGrpCat.{max w vJ} R).map α) ≫
        (bkVerticalHomologyCoefficientBarComplexIso R E q).hom =
      (bkVerticalHomologyCoefficientBarComplexIso R D q).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max w vJ}).map
          (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap
            (Functor.whiskerRight α (SSet.homologyFunctor R q))) := by
  apply HomologicalComplex.Hom.ext
  funext p
  dsimp only [bkVerticalHomologyCoefficientBarComplexIso, Iso.trans_hom,
    HomologicalComplex.comp_f, bkVerticalHomologyComplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  change
    (HomologicalComplex.homologyMap
        (((bkAlternatingBicomplexFunctor AddCommGrpCat.{max w vJ} R).map α).f p) q ≫
      (bkAlternatingVerticalHomologyIso R E p q).hom) ≫
        (CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          (E ⋙ SSet.homologyFunctor R q) p).hom =
      ((bkAlternatingVerticalHomologyIso R D p q).hom ≫
        (CategoryTheory.CategoryHomology.terminalWeightCoefficientBarDegreeIso
          (D ⋙ SSet.homologyFunctor R q) p).hom) ≫
        CategoryTheory.CategoryHomology.coefficientBarMap
          (Functor.whiskerRight α (SSet.homologyFunctor R q)) p
  rw [bkAlternatingVerticalHomologyIso_hom_naturality]
  rw [Category.assoc,
    terminalWeightCoefficientBarDegreeIso_hom_naturality]
  rfl

end SSet

end
