/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.OfFunctorHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology commutes with exact filtered colimits, canonically.

We construct the canonical comparison `homologyColimitIso` for a diagram
`K : J ⥤ HomologicalComplex C c` and prove the generator formulas for its
`hom` and `inv`, and that the inverse equals `colimit.post`.
-/

open CategoryTheory Limits

universe w w' v u t

namespace HomologicalComplex

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} {c : ComplexShape ι} [HasColimitsOfShape J C]

private noncomputable def colimitIsoColimOfFunctor (K : J ⥤ HomologicalComplex C c) :
    colimit K ≅ ((colim (J := J) (C := C)).mapHomologicalComplex c).obj (ofFunctor K) :=
  colimit.isoColimitCocone ⟨coconeOfHasColimitEval K, isColimitCoconeOfHasColimitEval K⟩

private lemma colimitIsoColimOfFunctor_ι (K : J ⥤ HomologicalComplex C c) (j : J) :
    colimit.ι K j ≫ (colimitIsoColimOfFunctor K).hom = (coconeOfHasColimitEval K).ι.app j := by
  change colimit.ι K j ≫ (colimit.isoColimitCocone _).hom = _
  exact colimit.isoColimitCocone_ι_hom _ j

variable [(colim (J := J) (C := C)).PreservesHomology]

/-- Canonical iso comparing homology of a colimit with the colimit of homologies. -/
public noncomputable def homologyColimitIso (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (colimit K).homology i ≅ colimit (K ⋙ homologyFunctor C c i) :=
  (homologyFunctor C c i).mapIso (colimitIsoColimOfFunctor K) ≪≫
    (mapHomologyFunctorIso i (colim (J := J) (C := C))).app (ofFunctor K) ≪≫
    (colim (J := J) (C := C)).mapIso (ofFunctorHomologyIso K i)

set_option backward.isDefEq.respectTransparency false in
/-- `map` of a colimit injection followed by the forward comparison is the target injection. -/
public theorem map_ι_comp_homologyColimitIso_hom (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (homologyFunctor C c i).map (colimit.ι K j) ≫ (homologyColimitIso K i).hom =
      colimit.ι (K ⋙ homologyFunctor C c i) j := by
  let S := (ofFunctor K).sc i
  let F := (evaluation J C).obj j
  let G := colim (J := J) (C := C)
  let τ : F ⟶ G := colim.ι j
  have hMap : S.mapNatTrans τ =
      (shortComplexFunctor C c i).map ((coconeOfHasColimitEval K).ι.app j) := rfl
  have hHomEq : homologyMap ((coconeOfHasColimitEval K).ι.app j) i =
      ShortComplex.homologyMap (S.mapNatTrans τ) := by
    calc homologyMap ((coconeOfHasColimitEval K).ι.app j) i
        = ShortComplex.homologyMap
            ((shortComplexFunctor C c i).map ((coconeOfHasColimitEval K).ι.app j)) := rfl
      _ = ShortComplex.homologyMap (S.mapNatTrans τ) := by rw [← hMap]
  let isoE := S.mapHomologyIso F
  let isoC := S.mapHomologyIso G
  let hIso := (ofFunctorHomologyIso K i).hom
  have hι : colimit.ι S.homology j ≫ G.map hIso =
      hIso.app j ≫ colimit.ι (K ⋙ homologyFunctor C c i) j := ι_colimMap hIso j
  have hAppJ : hIso.app j = isoE.inv := ofFunctorHomologyIso_hom_app K i j
  have hCancel : ShortComplex.homologyMap (S.mapNatTrans τ) ≫ isoC.hom ≫ G.map hIso =
      colimit.ι (K ⋙ homologyFunctor C c i) j := by
    rw [← NatTrans.mapHomologyIso_hom_comp_app_homology_assoc τ S]
    change isoE.hom ≫ (colimit.ι S.homology j ≫ G.map hIso) = _
    rw [hι, hAppJ, Iso.hom_inv_id_assoc]
  have hLeg : homologyMap (colimit.ι K j) i ≫ homologyMap (colimitIsoColimOfFunctor K).hom i =
      homologyMap ((coconeOfHasColimitEval K).ι.app j) i := by
    have hC : homologyMap (colimit.ι K j ≫ (colimitIsoColimOfFunctor K).hom) i =
        homologyMap (colimit.ι K j) i ≫ homologyMap (colimitIsoColimOfFunctor K).hom i :=
      homologyMap_comp _ _ i
    rw [← hC, colimitIsoColimOfFunctor_ι]
  calc (homologyFunctor C c i).map (colimit.ι K j) ≫ (homologyColimitIso K i).hom
      = homologyMap (colimit.ι K j) i ≫ homologyMap (colimitIsoColimOfFunctor K).hom i ≫
          isoC.hom ≫ G.map hIso := rfl
    _ = homologyMap ((coconeOfHasColimitEval K).ι.app j) i ≫ isoC.hom ≫ G.map hIso := by
        rw [← Category.assoc, hLeg]
    _ = ShortComplex.homologyMap (S.mapNatTrans τ) ≫ isoC.hom ≫ G.map hIso := by
        rw [hHomEq]
    _ = _ := hCancel

set_option backward.isDefEq.respectTransparency false in
/-- Target injection followed by the inverse comparison is the `map` of the source injection. -/
public theorem ι_comp_homologyColimitIso_inv (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    colimit.ι (K ⋙ homologyFunctor C c i) j ≫ (homologyColimitIso K i).inv =
      (homologyFunctor C c i).map (colimit.ι K j) := by
  have h := map_ι_comp_homologyColimitIso_hom (K := K) i j
  calc colimit.ι (K ⋙ homologyFunctor C c i) j ≫ (homologyColimitIso K i).inv
      = ((homologyFunctor C c i).map (colimit.ι K j) ≫ (homologyColimitIso K i).hom) ≫
          (homologyColimitIso K i).inv := by rw [h]
    _ = (homologyFunctor C c i).map (colimit.ι K j) ≫
          ((homologyColimitIso K i).hom ≫ (homologyColimitIso K i).inv) := by
        rw [Category.assoc]
    _ = _ := by rw [Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the canonical iso equals the colimit comparison map. -/
public theorem homologyColimitIso_inv_eq_colimit_post (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (homologyColimitIso K i).inv = colimit.post K (homologyFunctor C c i) := by
  apply colimit.hom_ext
  intro j
  have h1 := ι_comp_homologyColimitIso_inv (K := K) i j
  have h2 := colimit.ι_post (F := K) (G := homologyFunctor C c i) j
  exact h1.trans h2.symm

public noncomputable instance homologyFunctor_preservesColimitsOfShape (i : ι) :
    PreservesColimitsOfShape J (homologyFunctor C c i) where
  preservesColimit {K} := by
    have hpost : IsIso (colimit.post K (homologyFunctor C c i)) := by
      rw [← homologyColimitIso_inv_eq_colimit_post K i]
      exact (homologyColimitIso K i).isIso_inv
    exact preservesColimit_of_isIso_post (F := K) (G := homologyFunctor C c i)

end HomologicalComplex
