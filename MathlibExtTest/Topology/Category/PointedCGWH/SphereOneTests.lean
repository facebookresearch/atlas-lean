/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.PointedCGWH.SphereOne

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap

/-!
# Tests for the canonical pointed CGWH circle, sphere, and disk
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace MathlibExtTest.PointedCGWH.SphereOneTests

private theorem circleEndpoint (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ (SSet.boundary.{v} 1).toQuotient =
      (SSet.boundary.{v} 1).pointToQuotient := by
  rw [← SSet.boundary.ι_ι i, Category.assoc,
    (SSet.boundary.{v} 1).quotient_isPushout.w]
  rw [← Category.assoc]
  have h : SSet.boundary.ι i ≫
      SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1) =
        𝟙 (Δ[0] : SSet.{v}) := by
    apply SSet.stdSimplex.isTerminalObj₀.hom_ext
  rw [h, Category.id_comp]

private noncomputable def circleCofork :
    Cofork (SSet.stdSimplex.δ (0 : Fin 2))
      (SSet.stdSimplex.δ (1 : Fin 2)) :=
  Cofork.ofπ (SSet.boundary.{v} 1).toQuotient
    ((circleEndpoint.{v} 0).trans (circleEndpoint.{v} 1).symm)

private noncomputable def circleIsColimit :
    IsColimit circleCofork.{v} :=
  Cofork.IsColimit.mk _
    (fun s =>
      (SSet.boundary.{v} 1).quotient_isPushout.desc s.π
        (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) (by
          apply SSet.boundary.hom_ext
          intro i
          have hi : SSet.boundary.ι i ≫
              SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1) =
                𝟙 (Δ[0] : SSet.{v}) := by
            apply SSet.stdSimplex.isTerminalObj₀.hom_ext
          calc
            _ = SSet.stdSimplex.δ i ≫ s.π := by
              rw [← Category.assoc, SSet.boundary.ι_ι]
            _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π := by
              fin_cases i
              · rfl
              · exact s.condition.symm
            _ = _ := by rw [← Category.assoc, hi, Category.id_comp]))
    (fun s => by
      change (SSet.boundary.{v} 1).toQuotient ≫ _ = s.π
      exact (SSet.boundary.{v} 1).quotient_isPushout.inl_desc
        s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _)
    (fun s m hm => by
      apply (SSet.boundary.{v} 1).quotient_isPushout.hom_ext
      · have hqm : (SSet.boundary.{v} 1).toQuotient ≫ m = s.π := by
          have hπ : circleCofork.{v}.π =
              (SSet.boundary.{v} 1).toQuotient := Cofork.π_ofπ _ _
          rw [← hπ]
          exact hm
        rw [hqm]
        exact ((SSet.boundary.{v} 1).quotient_isPushout.inl_desc
          s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm
      · have hqm : (SSet.boundary.{v} 1).toQuotient ≫ m = s.π := by
          have hπ : circleCofork.{v}.π =
              (SSet.boundary.{v} 1).toQuotient := Cofork.π_ofπ _ _
          rw [← hπ]
          exact hm
        calc
          _ = (SSet.stdSimplex.δ (0 : Fin 2) ≫
                (SSet.boundary.{v} 1).toQuotient) ≫ m := by
            rw [circleEndpoint]
          _ = SSet.stdSimplex.δ (0 : Fin 2) ≫
                ((SSet.boundary.{v} 1).toQuotient ≫ m) :=
            Category.assoc _ _ _
          _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π := by rw [hqm]
          _ = _ := ((SSet.boundary.{v} 1).quotient_isPushout.inr_desc
            s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm)

section SimplicialCircle

example : SSet.pointedCircle.{v}.right =
    (SSet.boundary.{v} 1).quotient := rfl

example : SSet.pointedCircle.{v}.hom =
    (SSet.boundary.{v} 1).pointToQuotient := rfl

example (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ (SSet.boundary.{v} 1).toQuotient =
      (SSet.boundary.{v} 1).pointToQuotient := by
  rw [← SSet.boundary.ι_ι i, Category.assoc,
    (SSet.boundary.{v} 1).quotient_isPushout.w]
  rw [← Category.assoc]
  have h : SSet.boundary.ι i ≫
      SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1) =
        𝟙 (Δ[0] : SSet.{v}) := by
    apply SSet.stdSimplex.isTerminalObj₀.hom_ext
  rw [h, Category.id_comp]

example : IsPushout (SSet.boundary.{v} 1).ι
    (SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1))
    (SSet.boundary.{v} 1).toQuotient
    (SSet.boundary.{v} 1).pointToQuotient :=
  (SSet.boundary.{v} 1).quotient_isPushout

example (s : Cofork (SSet.stdSimplex.δ (0 : Fin 2))
    (SSet.stdSimplex.δ (1 : Fin 2))) :
    ∃! d : (SSet.boundary.{v} 1).quotient ⟶ s.pt,
      (SSet.boundary.{v} 1).toQuotient ≫ d = s.π := by
  have endpoint : ∀ i : Fin 2,
      SSet.stdSimplex.δ i ≫ (SSet.boundary.{v} 1).toQuotient =
        (SSet.boundary.{v} 1).pointToQuotient := fun i => by
    rw [← SSet.boundary.ι_ι i, Category.assoc,
      (SSet.boundary.{v} 1).quotient_isPushout.w]
    rw [← Category.assoc]
    have h : SSet.boundary.ι i ≫
        SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1) =
          𝟙 (Δ[0] : SSet.{v}) := by
      apply SSet.stdSimplex.isTerminalObj₀.hom_ext
    rw [h, Category.id_comp]
  let d := (SSet.boundary.{v} 1).quotient_isPushout.desc s.π
    (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) (by
      apply SSet.boundary.hom_ext
      intro i
      have hi : SSet.boundary.ι i ≫
          SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{v} 1) =
            𝟙 (Δ[0] : SSet.{v}) := by
        apply SSet.stdSimplex.isTerminalObj₀.hom_ext
      calc
        _ = SSet.stdSimplex.δ i ≫ s.π := by
          rw [← Category.assoc, SSet.boundary.ι_ι]
        _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π := by
          fin_cases i
          · rfl
          · exact s.condition.symm
        _ = _ := by rw [← Category.assoc, hi, Category.id_comp])
  refine ⟨d, ?_, ?_⟩
  · exact (SSet.boundary.{v} 1).quotient_isPushout.inl_desc
      s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _
  · intro m hm
    apply (SSet.boundary.{v} 1).quotient_isPushout.hom_ext
    · rw [hm]
      exact ((SSet.boundary.{v} 1).quotient_isPushout.inl_desc
        s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm
    · calc
        _ = (SSet.stdSimplex.δ (0 : Fin 2) ≫
              (SSet.boundary.{v} 1).toQuotient) ≫ m := by
          rw [endpoint]
        _ = SSet.stdSimplex.δ (0 : Fin 2) ≫
              ((SSet.boundary.{v} 1).toQuotient ≫ m) :=
          Category.assoc _ _ _
        _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π := by rw [hm]
        _ = _ := ((SSet.boundary.{v} 1).quotient_isPushout.inr_desc
          s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm

example :
    (SSet.boundary.{0} 1).toQuotient ≫
        SSet.pointedCircleIsoS1.hom =
      colimit.ι (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
        (SSet.stdSimplex.δ (1 : Fin 2))) WalkingParallelPair.one := by
  unfold SSet.pointedCircleIsoS1
  change (SSet.boundary.{0} 1).toQuotient ≫
      (circleIsColimit.{0}.coconePointUniqueUpToIso
        (colimit.isColimit _)).hom = _
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    circleIsColimit.{0}
    (colimit.isColimit
      (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
        (SSet.stdSimplex.δ (1 : Fin 2))))
    WalkingParallelPair.one

example :
    (SSet.boundary.{0} 1).pointToQuotient ≫
        SSet.pointedCircleIsoS1.hom =
      SSet.stdSimplex.δ (0 : Fin 2) ≫
        colimit.ι (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
          (SSet.stdSimplex.δ (1 : Fin 2))) WalkingParallelPair.one := by
  have hEndpoint : SSet.stdSimplex.δ (0 : Fin 2) ≫
        (SSet.boundary.{0} 1).toQuotient =
      (SSet.boundary.{0} 1).pointToQuotient := by
    rw [← SSet.boundary.ι_ι, Category.assoc,
      (SSet.boundary.{0} 1).quotient_isPushout.w]
    rw [← Category.assoc]
    have h : SSet.boundary.ι (0 : Fin 2) ≫
        SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{0} 1) =
          𝟙 (Δ[0] : SSet.{0}) := by
      apply SSet.stdSimplex.isTerminalObj₀.hom_ext
    rw [h, Category.id_comp]
  have hQuotient : (SSet.boundary.{0} 1).toQuotient ≫
        SSet.pointedCircleIsoS1.hom =
      colimit.ι (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
        (SSet.stdSimplex.δ (1 : Fin 2))) WalkingParallelPair.one := by
    unfold SSet.pointedCircleIsoS1
    change (SSet.boundary.{0} 1).toQuotient ≫
        (circleIsColimit.{0}.coconePointUniqueUpToIso
          (colimit.isColimit _)).hom = _
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      circleIsColimit.{0}
      (colimit.isColimit
        (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
          (SSet.stdSimplex.δ (1 : Fin 2))))
      WalkingParallelPair.one
  calc
    _ = (SSet.stdSimplex.δ (0 : Fin 2) ≫
          (SSet.boundary.{0} 1).toQuotient) ≫
        SSet.pointedCircleIsoS1.hom := by rw [hEndpoint]
    _ = SSet.stdSimplex.δ (0 : Fin 2) ≫
        ((SSet.boundary.{0} 1).toQuotient ≫
          SSet.pointedCircleIsoS1.hom) := Category.assoc _ _ _
    _ = _ := by
      rw [hQuotient]
      rfl

end SimplicialCircle

section NativeSphere

example : PointedCGWH.sphereOne.{u, v}.right =
    pushout
      (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι)
      (CGWH.point_isTerminal.from
        (SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1))) := rfl

example : PointedCGWH.sphereOne.{u, v}.hom =
    pushout.inr
      (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι)
      (CGWH.point_isTerminal.from
        (SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1))) := rfl

example :
    (SSet.pointedToCGWH.{u, v}.obj SSet.pointedCircle.{v}).hom ≫
        (PointedCGWH.pointedCircleRealizationIsoSphereOne.{u, v}).hom.right =
      PointedCGWH.sphereOne.{u, v}.hom :=
  Under.w (PointedCGWH.pointedCircleRealizationIsoSphereOne.{u, v}).hom

end NativeSphere

section Disk

example : PointedCGWH.diskOne.{u, v}.hom =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (0 : Fin 2) :
          (Δ[0] : SSet.{v}) ⟶ Δ[1]) := rfl

example :
    (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
      PointedCGWH.diskBoundary.{u, v}.right =
        PointedCGWH.diskOne.{u, v}.hom := by
  exact Under.w PointedCGWH.diskBoundary.{u, v}

example :
    (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
      PointedCGWH.diskBoundary.{u, v}.right =
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
          SSet.toCGWH.{u, v}.map
            (SSet.stdSimplex.δ (1 : Fin 2) :
              (Δ[0] : SSet.{v}) ⟶ Δ[1]) := by
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  change _ = e₀.inv ≫ SSet.toCGWH.{u, v}.map
    (SSet.stdSimplex.δ (1 : Fin 2))
  simp [PointedCGWH.diskBoundary, e₀]
  change (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ (1 : Fin 2)) = _
  rfl

example : ∃ e : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ≅
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v},
    e.hom ≫ PointedCGWH.diskBoundary.{u, v}.right =
        SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι ∧
    (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2)) ∧
    (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2)) := by
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  let eS : (SSet.boundary.{v} 1 : SSet.{v}) ≅
      ((Δ[0] : SSet.{v}) ⨿ (Δ[0] : SSet.{v})) := by
    let hom : (SSet.boundary.{v} 1 : SSet.{v}) ⟶
        ((Δ[0] : SSet.{v}) ⨿ (Δ[0] : SSet.{v})) :=
      SSet.boundaryOneMap
      (SSet.yonedaEquiv (coprod.inr :
        (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0]))
      (SSet.yonedaEquiv (coprod.inl :
        (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0]))
    let inv : ((Δ[0] : SSet.{v}) ⨿ (Δ[0] : SSet.{v})) ⟶
        (SSet.boundary.{v} 1 : SSet.{v}) :=
      coprod.desc (SSet.boundary.ι (0 : Fin 2))
        (SSet.boundary.ι (1 : Fin 2))
    exact
      { hom := hom
        inv := inv
        hom_inv_id := by
          apply SSet.boundary.hom_ext
          intro i
          fin_cases i
          · change (SSet.boundary.ι (0 : Fin 2) ≫ hom) ≫ inv =
              SSet.boundary.ι (0 : Fin 2) ≫ 𝟙 _
            simp [hom, inv, ← SSet.yonedaEquiv_symm_zero]
          · change (SSet.boundary.ι (1 : Fin 2) ≫ hom) ≫ inv =
              SSet.boundary.ι (1 : Fin 2) ≫ 𝟙 _
            simp [hom, inv, ← SSet.yonedaEquiv_symm_zero]
        inv_hom_id := by
          apply Limits.coprod.hom_ext <;>
            simp [hom, inv, ← SSet.yonedaEquiv_symm_zero] }
  let e := SSet.toCGWH.mapIso eS ≪≫
      preservesColimitIso SSet.toCGWH.{u, v}
        (pair (Δ[0] : SSet.{v}) Δ[0]) ≪≫
      HasColimit.isoOfNatIso
        (pairComp (Δ[0] : SSet.{v}) Δ[0] SSet.toCGWH.{u, v}) ≪≫
      coprod.mapIso e₀ e₀
  have h₀ : (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2)) := by
    change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))
    simp [e, eS, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (0 : Fin 2)) = _
    rw [Category.id_comp]
  have h₁ : (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2)) := by
    change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2))
    simp [e, eS, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (1 : Fin 2)) = _
    rw [Category.id_comp]
  let p₀ : CGWH.point.{u, v} ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
    e₀.inv ≫ SSet.toCGWH.{u, v}.map
      (SSet.stdSimplex.δ (0 : Fin 2))
  let p₁ : CGWH.point.{u, v} ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
    e₀.inv ≫ SSet.toCGWH.{u, v}.map
      (SSet.stdSimplex.δ (1 : Fin 2))
  let d : CGWH.point.{u, v} ⨿ CGWH.point.{u, v} ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
    coprod.desc p₀ p₁
  have hDisk : PointedCGWH.diskBoundary.{u, v}.right = d := rfl
  have hInv : e.inv ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.{v} 1).ι =
      d := by
    apply Limits.coprod.hom_ext
    · calc
        _ = ((coprod.inl : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι :=
          (Category.assoc _ _ _).symm
        _ = ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
              SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (0 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι := by rw [h₀]
        _ = p₀ := by
          change (e₀.inv ≫ SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (0 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι = p₀
          rw [Category.assoc, ← Functor.map_comp,
            SSet.boundary.ι_ι]
        _ = _ := (Limits.coprod.inl_desc p₀ p₁).symm
    · calc
        _ = ((coprod.inr : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι :=
          (Category.assoc _ _ _).symm
        _ = ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
              SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (1 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι := by rw [h₁]
        _ = p₁ := by
          change (e₀.inv ≫ SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (1 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι = p₁
          rw [Category.assoc, ← Functor.map_comp,
            SSet.boundary.ι_ι]
        _ = _ := (Limits.coprod.inr_desc p₀ p₁).symm
  refine ⟨e, ?_, h₀, h₁⟩
  calc
    _ = e.hom ≫ d := congrArg (fun k => e.hom ≫ k) hDisk
    _ = e.hom ≫ (e.inv ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι) := by rw [hInv]
    _ = (e.hom ≫ e.inv) ≫
        SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [Iso.hom_inv_id, Category.id_comp]

example :
    PointedCGWH.diskOne.{u, v}.hom ≫
        PointedCGWH.diskAugmentation.{u, v}.right =
      (⊤_ PointedCGWH.{u, v}).hom :=
  Under.w PointedCGWH.diskAugmentation.{u, v}

example :
    (HomotopicalAlgebra.ordinaryCofiber
      (C := PointedCGWH.{u, v})).obj
        (Arrow.mk PointedCGWH.diskBoundary.{u, v}) ≅
      PointedCGWH.sphereOne.{u, v} :=
  PointedCGWH.diskCofiberIsoSphereOne.{u, v}

example :
    (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).hom.right ≫
        (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).inv.right =
      𝟙 _ :=
  Under.hom_right_inv_right _

example :
    (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).inv.right ≫
        (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).hom.right =
      𝟙 _ :=
  Under.inv_right_hom_right _

example :
    ((HomotopicalAlgebra.ordinaryCofiber
      (C := PointedCGWH.{u, v})).obj
        (Arrow.mk PointedCGWH.diskBoundary.{u, v})).hom ≫
        (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).hom.right =
      PointedCGWH.sphereOne.{u, v}.hom :=
  Under.w (PointedCGWH.diskCofiberIsoSphereOne.{u, v}).hom

end Disk

section UniverseMatrix

#check SSet.pointedCircle.{0}
#check SSet.pointedCircle.{1}
#check SSet.pointedCircle.{v}
#check SSet.pointedCircleIsoS1

#check PointedCGWH.sphereOne.{0, 0}
#check PointedCGWH.sphereOne.{1, 1}
#check PointedCGWH.sphereOne.{0, 1}
#check PointedCGWH.sphereOne.{1, 0}
#check PointedCGWH.sphereOne.{u, v}

#check PointedCGWH.pointedCircleRealizationIsoSphereOne.{0, 0}
#check PointedCGWH.pointedCircleRealizationIsoSphereOne.{1, 1}
#check PointedCGWH.pointedCircleRealizationIsoSphereOne.{0, 1}
#check PointedCGWH.pointedCircleRealizationIsoSphereOne.{1, 0}
#check PointedCGWH.pointedCircleRealizationIsoSphereOne.{u, v}

#check PointedCGWH.diskOne.{0, 0}
#check PointedCGWH.diskBoundary.{1, 1}
#check PointedCGWH.diskAugmentation.{0, 1}
#check PointedCGWH.diskCofiberIsoSphereOne.{1, 0}

end UniverseMatrix

section NegativeBoundaries

#guard_msgs (error, substring := true) in
#check SSet.S1.{1}

#guard_msgs (error, substring := true) in
example : SSet.pointedCircle.{1}.right = SSet.S1 := by rfl

#guard_msgs (error, substring := true) in
#check PointedCGWH.smash

#guard_msgs (error, substring := true) in
#check PointedCGWH.suspension

#guard_msgs (error, substring := true) in
#check PointedCGWH.modelCategory.sphereOne_isCofibrant

#guard_msgs (error, substring := true) in
#check PointedCGWH.orthogonalSphere

end NegativeBoundaries

#print axioms SSet.pointedCircle
#print axioms SSet.pointedCircleIsoS1
#print axioms PointedCGWH.sphereOne
#print axioms PointedCGWH.pointedCircleRealizationIsoSphereOne
#print axioms PointedCGWH.diskOne
#print axioms PointedCGWH.diskBoundary
#print axioms PointedCGWH.diskAugmentation
#print axioms PointedCGWH.diskCofiberIsoSphereOne

end MathlibExtTest.PointedCGWH.SphereOneTests
