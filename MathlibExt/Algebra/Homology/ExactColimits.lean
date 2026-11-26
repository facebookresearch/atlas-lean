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
# Homology commutes with homology-preserving colimits

Let `C` be abelian with colimits of an arbitrary shape `J`, and
suppose the colimit functor preserves homology. For a diagram of
complexes of any shape `c`, there is a canonical comparison
`H_i(colim K) ≅ colim_j H_i(K_j)`. It preserves the original diagram
injections, and its inverse is the colimit comparison induced by
the homology functor. The category and complex-index worlds are independent.
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

/-- Let `C` be abelian with colimits of shape `J`, where `J` is
any category, and suppose `colim : (J → C) → C` preserves homology.
Let `c` be any complex shape and `K : J → HomologicalComplex C c`. For each complex index `i`, there is a canonical isomorphism
`H_i(colim K) ≅ colim_j H_i(K_j)`. -/
public noncomputable def homologyColimitIso (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (colimit K).homology i ≅ colimit (K ⋙ homologyFunctor C c i) :=
  (homologyFunctor C c i).mapIso (colimitIsoColimOfFunctor K) ≪≫
    (mapHomologyFunctorIso i (colim (J := J) (C := C))).app (ofFunctor K) ≪≫
    (colim (J := J) (C := C)).mapIso (ofFunctorHomologyIso K i)

set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be abelian with colimits of shape `J`, where `J` is
any category, and suppose `colim : (J → C) → C` preserves homology.
Let `c` be any complex shape and `K : J → HomologicalComplex C c`. For `j : J`, taking homology of `K_j → colim K` and then
the forward comparison gives the injection
`H_i(K_j) → colim_l H_i(K_l)`. -/
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
/-- Let `C` be abelian with colimits of shape `J`, where `J` is
any category, and suppose `colim : (J → C) → C` preserves homology.
Let `c` be any complex shape and `K : J → HomologicalComplex C c`. For `j : J`, the injection `H_i(K_j) → colim_l H_i(K_l)`
followed by the inverse comparison is the homology map of
`K_j → colim K`. -/
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
/-- Let `C` be abelian with colimits of shape `J`, where `J` is
any category, and suppose `colim : (J → C) → C` preserves homology.
Let `c` be any complex shape and `K : J → HomologicalComplex C c`. The inverse comparison from `colim_j H_i(K_j)` to
`H_i(colim K)` is the canonical colimit comparison induced by the
homology functor. -/
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
