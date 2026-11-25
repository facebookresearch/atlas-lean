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
# Homology commutes with exact limits, canonically.

We construct the canonical comparison `homologyLimitIso` for a diagram
`K : J ⥤ HomologicalComplex C c` and prove the generator formulas for its
`hom` and `inv`, and that the forward map equals `limit.post`.
-/

open CategoryTheory Limits

universe w w' v u t

namespace HomologicalComplex

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} {c : ComplexShape ι} [HasLimitsOfShape J C]

private noncomputable def limitIsoLimOfFunctor (K : J ⥤ HomologicalComplex C c) :
    limit K ≅ ((lim (J := J) (C := C)).mapHomologicalComplex c).obj (ofFunctor K) :=
  limit.isoLimitCone ⟨coneOfHasLimitEval K, isLimitConeOfHasLimitEval K⟩

private lemma limitIsoLimOfFunctor_π (K : J ⥤ HomologicalComplex C c) (j : J) :
    (limitIsoLimOfFunctor K).hom ≫ (coneOfHasLimitEval K).π.app j = limit.π K j := by
  change (limit.isoLimitCone _).hom ≫ _ = _
  exact limit.isoLimitCone_hom_π _ j

variable [(lim (J := J) (C := C)).PreservesHomology]

/-- Canonical iso comparing homology of a limit with the limit of homologies. -/
public noncomputable def homologyLimitIso (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (limit K).homology i ≅ limit (K ⋙ homologyFunctor C c i) :=
  (homologyFunctor C c i).mapIso (limitIsoLimOfFunctor K) ≪≫
    (mapHomologyFunctorIso i (lim (J := J) (C := C))).app (ofFunctor K) ≪≫
    (lim (J := J) (C := C)).mapIso (ofFunctorHomologyIso K i)

set_option backward.isDefEq.respectTransparency false in
/-- The forward comparison followed by a limit projection is the homology map of the projection. -/
public theorem homologyLimitIso_hom_comp_π (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (homologyLimitIso K i).hom ≫ limit.π (K ⋙ homologyFunctor C c i) j =
      (homologyFunctor C c i).map (limit.π K j) := by
  let S := (ofFunctor K).sc i
  let F := (lim (J := J) (C := C))
  let E := (evaluation J C).obj j
  let τ : F ⟶ E := lim.π j
  have hMap : S.mapNatTrans τ =
      (shortComplexFunctor C c i).map ((coneOfHasLimitEval K).π.app j) := rfl
  have hHomEq : homologyMap ((coneOfHasLimitEval K).π.app j) i =
      ShortComplex.homologyMap (S.mapNatTrans τ) := by
    calc homologyMap ((coneOfHasLimitEval K).π.app j) i
        = ShortComplex.homologyMap
            ((shortComplexFunctor C c i).map ((coneOfHasLimitEval K).π.app j)) := rfl
      _ = ShortComplex.homologyMap (S.mapNatTrans τ) := by rw [← hMap]
  let isoE := S.mapHomologyIso E
  let isoL := S.mapHomologyIso F
  let hIso := (ofFunctorHomologyIso K i).hom
  have hπ : F.map hIso ≫ τ.app (K ⋙ homologyFunctor C c i) =
      τ.app S.homology ≫ E.map hIso := τ.naturality hIso
  have hπ' : F.map hIso ≫ limit.π (K ⋙ homologyFunctor C c i) j =
      limit.π S.homology j ≫ hIso.app j := by
    simpa [E, τ] using hπ
  have hAppJ : hIso.app j = isoE.inv := ofFunctorHomologyIso_hom_app K i j
  have hCancel : F.map hIso ≫ limit.π (K ⋙ homologyFunctor C c i) j =
      isoL.inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ) := by
    rw [hπ', hAppJ]
    exact NatTrans.app_homology_comp_mapHomologyIso_inv τ S
  have hLeg : homologyMap (limitIsoLimOfFunctor K).hom i ≫
      homologyMap ((coneOfHasLimitEval K).π.app j) i =
      homologyMap (limit.π K j) i := by
    have hC : homologyMap ((limitIsoLimOfFunctor K).hom ≫ (coneOfHasLimitEval K).π.app j) i =
        homologyMap (limitIsoLimOfFunctor K).hom i ≫
          homologyMap ((coneOfHasLimitEval K).π.app j) i :=
      homologyMap_comp _ _ i
    rw [← hC, limitIsoLimOfFunctor_π]
  have hHom : (homologyLimitIso K i).hom =
      homologyMap (limitIsoLimOfFunctor K).hom i ≫
        (mapHomologyFunctorIso i F).hom.app (ofFunctor K) ≫ F.map hIso := rfl
  calc (homologyLimitIso K i).hom ≫ limit.π (K ⋙ homologyFunctor C c i) j
      = (homologyMap (limitIsoLimOfFunctor K).hom i ≫
          (mapHomologyFunctorIso i F).hom.app (ofFunctor K) ≫ F.map hIso) ≫
            limit.π (K ⋙ homologyFunctor C c i) j := by
        rw [hHom]
    _ = homologyMap (limitIsoLimOfFunctor K).hom i ≫
          (mapHomologyFunctorIso i F).hom.app (ofFunctor K) ≫
            F.map hIso ≫ limit.π (K ⋙ homologyFunctor C c i) j := by
        simp only [Category.assoc]
    _ = homologyMap (limitIsoLimOfFunctor K).hom i ≫
          isoL.hom ≫ F.map hIso ≫ limit.π (K ⋙ homologyFunctor C c i) j := rfl
    _ = homologyMap (limitIsoLimOfFunctor K).hom i ≫
          isoL.hom ≫ (isoL.inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ)) := by
        rw [hCancel]
    _ = homologyMap (limitIsoLimOfFunctor K).hom i ≫
          ShortComplex.homologyMap (S.mapNatTrans τ) := by
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = homologyMap (limitIsoLimOfFunctor K).hom i ≫
          homologyMap ((coneOfHasLimitEval K).π.app j) i := by
        rw [hHomEq]
    _ = homologyMap (limit.π K j) i := hLeg
    _ = (homologyFunctor C c i).map (limit.π K j) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison followed by the homology map of a projection is the target projection. -/
public theorem homologyLimitIso_inv_comp_map_π (K : J ⥤ HomologicalComplex C c) (i : ι) (j : J) :
    (homologyLimitIso K i).inv ≫ (homologyFunctor C c i).map (limit.π K j) =
      limit.π (K ⋙ homologyFunctor C c i) j := by
  have h := homologyLimitIso_hom_comp_π (K := K) i j
  calc (homologyLimitIso K i).inv ≫ (homologyFunctor C c i).map (limit.π K j)
      = (homologyLimitIso K i).inv ≫
          ((homologyLimitIso K i).hom ≫ limit.π (K ⋙ homologyFunctor C c i) j) := by
        rw [h]
    _ = ((homologyLimitIso K i).inv ≫ (homologyLimitIso K i).hom) ≫
          limit.π (K ⋙ homologyFunctor C c i) j := by
        rw [Category.assoc]
    _ = _ := by rw [Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The forward comparison equals the limit comparison map. -/
public theorem homologyLimitIso_hom_eq_limit_post (K : J ⥤ HomologicalComplex C c) (i : ι) :
    (homologyLimitIso K i).hom = limit.post K (homologyFunctor C c i) := by
  apply limit.hom_ext
  intro j
  have h1 := homologyLimitIso_hom_comp_π (K := K) i j
  have h2 : limit.post K (homologyFunctor C c i) ≫
      limit.π (K ⋙ homologyFunctor C c i) j =
      (homologyFunctor C c i).map (limit.π K j) := by
    simp [limit.post]
  rw [h1, h2]

public noncomputable instance homologyFunctor_preservesLimitsOfShape (i : ι) :
    PreservesLimitsOfShape J (homologyFunctor C c i) where
  preservesLimit {K} := by
    have hpost : IsIso (limit.post K (homologyFunctor C c i)) := by
      rw [← homologyLimitIso_hom_eq_limit_post (K := K) i]
      exact (homologyLimitIso (K := K) i).isIso_hom
    exact preservesLimit_of_isIso_post (F := K) (G := homologyFunctor C c i)

end HomologicalComplex
