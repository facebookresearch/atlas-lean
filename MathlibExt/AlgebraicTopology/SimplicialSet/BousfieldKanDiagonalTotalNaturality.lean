/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotal
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of common-universe Bousfield--Kan chain comparisons

The fixed carrier-chain presentation and both original Alexander--Whitney
and shuffle maps commute with the actual diagram maps. The original
homology naturality theorem retains its coefficient and degree arguments.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

noncomputable section

universe uJ vJ uA vA

namespace HomotopyEquiv

variable {V : Type uA} [Category.{vA} V] [Preadditive V] {ι : Type*}
  {c : ComplexShape ι} {K L K' L' : HomologicalComplex V c}

/-- Naturality of the homology isomorphism of a homotopy equivalence in its
forward map. -/
private theorem toHomologyIso_naturality (e : HomotopyEquiv K L)
    (e' : HomotopyEquiv K' L') (f : K ⟶ K') (g : L ⟶ L') (i : ι)
    [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]
    (h : f ≫ e'.hom = e.hom ≫ g) :
    HomologicalComplex.homologyMap f i ≫ (e'.toHomologyIso i).hom =
      (e.toHomologyIso i).hom ≫ HomologicalComplex.homologyMap g i := by
  change HomologicalComplex.homologyMap f i ≫
      HomologicalComplex.homologyMap e'.hom i =
    HomologicalComplex.homologyMap e.hom i ≫ HomologicalComplex.homologyMap g i
  exact HomologicalComplex.homologyMap_square h i

end HomotopyEquiv

namespace SSet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ComparisonNaturality

variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uJ vJ} A] [HasCountableCoproducts A]
  {J : Type uJ} [Category.{vJ} J] {D E : J ⥤ SSet.{max uJ vJ}}
  (R : A)

private abbrev bkLinearizedBarMap (alpha : D ⟶ E) :
    bkLinearizedBisimplicial A R D ⟶ bkLinearizedBisimplicial A R E :=
  (bisimplicialLinearizationFunctor A R).map
    ((bkBarBisimplicialFunctor (J := J)).map alpha)

private abbrev bkLinearizedCarrierMap (alpha : D ⟶ E) :
    bkLinearizedHocolim A R D ⟶ bkLinearizedHocolim A R E :=
  (coproductLinearizationFunctor A R).map (bkHocolimMap alpha)

private abbrev bkDiagonalChainMap (alpha : D ⟶ E) :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map
    ((SimplicialObject.diagonalFunctor A).map (bkLinearizedBarMap A R alpha))

private abbrev bkCarrierChainMap (alpha : D ⟶ E) :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map
    (bkLinearizedCarrierMap A R alpha)

omit [HasCountableCoproducts A] in
/-- This typed presentation retains the actual simplicial chain map. -/
theorem bkCarrierChainIso_naturality (alpha : D ⟶ E) :
    SSet.chainComplexMap (bkHocolimMap alpha) R ≫
        (bkCarrierChainIso A R E).hom =
      (bkCarrierChainIso A R D).hom ≫ (AlgebraicTopology.alternatingFaceMapComplex A).map
        ((coproductLinearizationFunctor A R).map (bkHocolimMap alpha)) := by
  have heD : (bkCarrierChainIso A R D).hom = 𝟙 _ := rfl
  have heE : (bkCarrierChainIso A R E).hom = 𝟙 _ := rfl
  have hm : SSet.chainComplexMap (bkHocolimMap alpha) R =
      bkCarrierChainMap A R alpha := rfl
  exact (congrArg (fun f => SSet.chainComplexMap (bkHocolimMap alpha) R ≫ f)
      heE).trans
    ((Category.comp_id _).trans
      (hm.trans ((Category.id_comp _).symm.trans
        (congrArg (fun f => f ≫ bkCarrierChainMap A R alpha) heD).symm)))

omit [Preadditive A] [HasCountableCoproducts A] in
/-- The actual pointwise diagonal comparison is natural. -/
private theorem bkDiagonalLinearizationIso_naturality (alpha : D ⟶ E) :
    (SimplicialObject.diagonalFunctor A).map (bkLinearizedBarMap A R alpha) ≫
        (bkDiagonalLinearizationIso A R E).hom =
      (bkDiagonalLinearizationIso A R D).hom ≫
        bkLinearizedCarrierMap A R alpha := by
  ext a
  have heD : (bkDiagonalLinearizationIso A R D).hom.app a = 𝟙 _ := rfl
  have heE : (bkDiagonalLinearizationIso A R E).hom.app a = 𝟙 _ := rfl
  have hm :
      ((SimplicialObject.diagonalFunctor A).map
        (bkLinearizedBarMap A R alpha)).app a =
      (bkLinearizedCarrierMap A R alpha).app a := rfl
  change _ ≫ (bkDiagonalLinearizationIso A R E).hom.app a =
    (bkDiagonalLinearizationIso A R D).hom.app a ≫ _
  exact (congrArg (fun f =>
      ((SimplicialObject.diagonalFunctor A).map
        (bkLinearizedBarMap A R alpha)).app a ≫ f) heE).trans
    ((Category.comp_id _).trans
      (hm.trans ((Category.id_comp _).symm.trans
        (congrArg (fun f => f ≫ (bkLinearizedCarrierMap A R alpha).app a)
          heD).symm)))

omit [Preadditive A] [HasCountableCoproducts A] in
private theorem bkDiagonalLinearizationIso_inv_naturality (alpha : D ⟶ E) :
    bkLinearizedCarrierMap A R alpha ≫ (bkDiagonalLinearizationIso A R E).inv =
      (bkDiagonalLinearizationIso A R D).inv ≫
        (SimplicialObject.diagonalFunctor A).map (bkLinearizedBarMap A R alpha) := by
  have h := congrArg (fun f =>
    (bkDiagonalLinearizationIso A R D).inv ≫ f ≫
      (bkDiagonalLinearizationIso A R E).inv)
    (bkDiagonalLinearizationIso_naturality A R alpha)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h.symm

omit [HasCountableCoproducts A] in
/-- Its alternating chain comparison is natural with the actual maps. -/
private theorem bkDiagonalAlternatingComplexIso_naturality (alpha : D ⟶ E) :
    bkDiagonalChainMap A R alpha ≫
        (bkDiagonalAlternatingComplexIso A R E).hom =
      (bkDiagonalAlternatingComplexIso A R D).hom ≫
        bkCarrierChainMap A R alpha := by
  exact (AlgebraicTopology.alternatingFaceMapComplex A).congr_map
    (bkDiagonalLinearizationIso_naturality A R alpha)

omit [HasCountableCoproducts A] in
private theorem bkDiagonalAlternatingComplexIso_inv_naturality (alpha : D ⟶ E) :
    bkCarrierChainMap A R alpha ≫
        (bkDiagonalAlternatingComplexIso A R E).inv =
      (bkDiagonalAlternatingComplexIso A R D).inv ≫
        bkDiagonalChainMap A R alpha := by
  have h := congrArg (fun f =>
    (bkDiagonalAlternatingComplexIso A R D).inv ≫ f ≫
      (bkDiagonalAlternatingComplexIso A R E).inv)
    (bkDiagonalAlternatingComplexIso_naturality A R alpha)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h.symm

/-- Naturality of the original Alexander–Whitney half. -/
theorem bkDiagonalTotalHomotopyEquiv_hom_naturality (alpha : D ⟶ E) :
    (AlgebraicTopology.alternatingFaceMapComplex A).map
        ((coproductLinearizationFunctor A R).map (bkHocolimMap alpha)) ≫
        (bkDiagonalTotalHomotopyEquiv A R E).hom =
      (bkDiagonalTotalHomotopyEquiv A R D).hom ≫
        (bkAlternatingTotalComplexFunctor A R).map alpha := by
  change bkCarrierChainMap A R alpha ≫
      ((bkDiagonalAlternatingComplexIso A R E).inv ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap _) =
    ((bkDiagonalAlternatingComplexIso A R D).inv ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap _) ≫ _
  rw [← Category.assoc, bkDiagonalAlternatingComplexIso_inv_naturality,
    Category.assoc,
    AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap_naturality,
    ← Category.assoc]
  rfl

/-- Naturality of the original shuffle half. -/
theorem bkDiagonalTotalHomotopyEquiv_inv_naturality (alpha : D ⟶ E) :
    (bkAlternatingTotalComplexFunctor A R).map alpha ≫
        (bkDiagonalTotalHomotopyEquiv A R E).inv =
      (bkDiagonalTotalHomotopyEquiv A R D).inv ≫
        (AlgebraicTopology.alternatingFaceMapComplex A).map
        ((coproductLinearizationFunctor A R).map (bkHocolimMap alpha)) := by
  have hS : (bkAlternatingTotalComplexFunctor A R).map alpha ≫
      AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (bkLinearizedBisimplicial A R E) =
    AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
        (bkLinearizedBisimplicial A R D) ≫ bkDiagonalChainMap A R alpha :=
    AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap_naturality
      (bkLinearizedBarMap A R alpha)
  change (bkAlternatingTotalComplexFunctor A R).map alpha ≫
      (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap _ ≫
        (bkDiagonalAlternatingComplexIso A R E).hom) =
    (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap _ ≫
        (bkDiagonalAlternatingComplexIso A R D).hom) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (bkDiagonalAlternatingComplexIso A R E).hom) hS).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f =>
          AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap
            (bkLinearizedBisimplicial A R D) ≫ f)
          (bkDiagonalAlternatingComplexIso_naturality A R alpha)).trans
          (Category.assoc _ _ _).symm)))


end ComparisonNaturality

section Homology

variable {J : Type uJ} [Category.{vJ} J]

/-- The original diagonal--total homology comparison is natural in the diagram. -/
theorem bkDiagonalTotalHomologyIso_naturality (R : AddCommGrpCat.{max uJ vJ})
    {D E : J ⥤ SSet.{max uJ vJ}} (alpha : D ⟶ E) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max uJ vJ}).map
            ((coproductLinearizationFunctor AddCommGrpCat.{max uJ vJ} R).map
              (bkHocolimMap alpha))) n ≫
        (bkDiagonalTotalHomologyIso R E n).hom =
      (bkDiagonalTotalHomologyIso R D n).hom ≫
        HomologicalComplex.homologyMap
          ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{max uJ vJ} R).map alpha) n :=
  HomotopyEquiv.toHomologyIso_naturality _ _ _ _ n
    (bkDiagonalTotalHomotopyEquiv_hom_naturality AddCommGrpCat.{max uJ vJ} R alpha)

end Homology

end SSet
