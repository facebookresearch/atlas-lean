/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHPointedRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexQuotient
public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.CGWH.Products
public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.CategoryTheory.Limits.Shapes.Cofiber
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap

/-!
# The canonical circle, sphere, and disk in pointed CGWH spaces

The simplicial circle is the quotient of the one-simplex by its full
boundary.  Its direct CGWH realization is compared with the native pushout
which collapses the realized boundary.  The interval with its two ordered
endpoints gives a model-free disk and an ordinary pointed cofiber
presentation of the same sphere.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace SSet

/-- The universe-polymorphic simplicial circle, pointed at its collapsed
boundary. -/
noncomputable def pointedCircle : Under (Δ[0] : SSet.{v}) :=
  Under.mk (SSet.boundary.{v} 1).pointToQuotient

private theorem pointedCircle_endpoint (i : Fin 2) :
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

/-- At universe zero, the boundary-quotient circle is canonically isomorphic
to Mathlib's colimit presentation of `SSet.S1`. -/
noncomputable def pointedCircleIsoS1 :
    SSet.pointedCircle.{0}.right ≅ SSet.S1 := by
  let t : Cofork (SSet.stdSimplex.δ (0 : Fin 2))
      (SSet.stdSimplex.δ (1 : Fin 2)) :=
    Cofork.ofπ (SSet.boundary.{0} 1).toQuotient
      ((pointedCircle_endpoint.{0} 0).trans
        (pointedCircle_endpoint.{0} 1).symm)
  let ht : IsColimit t := Cofork.IsColimit.mk _
    (fun s =>
      (SSet.boundary.{0} 1).quotient_isPushout.desc s.π
        (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) (by
          apply SSet.boundary.hom_ext
          intro i
          have hi : SSet.boundary.ι i ≫
              SSet.stdSimplex.isTerminalObj₀.from (SSet.boundary.{0} 1) =
                𝟙 (Δ[0] : SSet.{0}) := by
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
      change (SSet.boundary.{0} 1).toQuotient ≫ _ = s.π
      exact (SSet.boundary.{0} 1).quotient_isPushout.inl_desc
        s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _)
    (fun s m hm => by
      apply (SSet.boundary.{0} 1).quotient_isPushout.hom_ext
      · have hqm : (SSet.boundary.{0} 1).toQuotient ≫ m = s.π := by
          have hπ : t.π = (SSet.boundary.{0} 1).toQuotient :=
            Cofork.π_ofπ _ _
          rw [← hπ]
          exact hm
        rw [hqm]
        exact ((SSet.boundary.{0} 1).quotient_isPushout.inl_desc
          s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm
      · have hqm : (SSet.boundary.{0} 1).toQuotient ≫ m = s.π := by
          have hπ : t.π = (SSet.boundary.{0} 1).toQuotient :=
            Cofork.π_ofπ _ _
          rw [← hπ]
          exact hm
        calc
          _ = (SSet.stdSimplex.δ (0 : Fin 2) ≫
                (SSet.boundary.{0} 1).toQuotient) ≫ m := by
            rw [pointedCircle_endpoint]
          _ = SSet.stdSimplex.δ (0 : Fin 2) ≫
                ((SSet.boundary.{0} 1).toQuotient ≫ m) :=
            Category.assoc _ _ _
          _ = SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π := by rw [hqm]
          _ = _ := ((SSet.boundary.{0} 1).quotient_isPushout.inr_desc
            s.π (SSet.stdSimplex.δ (0 : Fin 2) ≫ s.π) _).symm)
  exact ht.coconePointUniqueUpToIso
    (colimit.isColimit
      (parallelPair (SSet.stdSimplex.δ (0 : Fin 2))
        (SSet.stdSimplex.δ (1 : Fin 2))))


end SSet

namespace PointedCGWH

private noncomputable def boundaryOneInclusion :
    SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}) :=
  SSet.toCGWH.map (SSet.boundary.{v} 1).ι

private noncomputable def boundaryOneCollapse :
    SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ⟶
      CGWH.point.{u, v} :=
  CGWH.point_isTerminal.from _

/-- The native pointed CGWH one-sphere, obtained by collapsing the realized
boundary of the one-simplex. -/
noncomputable def sphereOne : PointedCGWH.{u, v} :=
  Under.mk (pushout.inr (boundaryOneInclusion.{u, v})
    (boundaryOneCollapse.{u, v}))

private theorem pointedCircleRealizationIsPushout :
    IsPushout
      (boundaryOneInclusion.{u, v})
      (boundaryOneCollapse.{u, v})
      (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).toQuotient)
      ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map
          (SSet.boundary.{v} 1).pointToQuotient) := by
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let h := (SSet.boundary.{v} 1).quotient_isPushout.map
    SSet.toCGWH.{u, v}
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  apply h.of_iso (Iso.refl _) (Iso.refl _) e₀ (Iso.refl _)
  · simp [boundaryOneInclusion]
  · apply CGWH.point_isTerminal.hom_ext
  · simp
  · exact (e₀.hom_inv_id_assoc _).symm

/-- Direct pointed realization of the simplicial boundary quotient agrees
with the native CGWH one-sphere. -/
noncomputable def pointedCircleRealizationIsoSphereOne :
    SSet.pointedToCGWH.{u, v}.obj SSet.pointedCircle.{v} ≅
      PointedCGWH.sphereOne.{u, v} := by
  let h₁ := pointedCircleRealizationIsPushout.{u, v}
  let h₂ := IsPushout.of_hasPushout
    (boundaryOneInclusion.{u, v}) (boundaryOneCollapse.{u, v})
  let e := h₁.isoIsPushout _ _ h₂
  exact Under.isoMk e (by
    change ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map
          (SSet.boundary.{v} 1).pointToQuotient) ≫ e.hom =
      pushout.inr (boundaryOneInclusion.{u, v})
        (boundaryOneCollapse.{u, v})
    exact h₁.inr_isoIsPushout_hom _ _ h₂)

set_option linter.flexible false in
private noncomputable def boundaryOneRealizationData :
    {e : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ≅
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v} //
      ((coprod.inl : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))) ∧
      ((coprod.inr : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2)))} := by
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  let e := SSet.toCGWH.mapIso SSet.boundaryOneIsoTwoPoints.{v} ≪≫
      preservesColimitIso SSet.toCGWH.{u, v}
        (pair (Δ[0] : SSet.{v}) Δ[0]) ≪≫
      HasColimit.isoOfNatIso
        (pairComp (Δ[0] : SSet.{v}) Δ[0] SSet.toCGWH.{u, v}) ≪≫
      coprod.mapIso e₀ e₀
  refine ⟨e, ?_, ?_⟩
  · change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))
    simp [e, SSet.boundaryOneIsoTwoPoints_inv, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (0 : Fin 2)) = _
    rw [Category.id_comp]
  · change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2))
    simp [e, SSet.boundaryOneIsoTwoPoints_inv, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (1 : Fin 2)) = _
    rw [Category.id_comp]

/-- The native one-disk, pointed at the endpoint `δ 0` (time one). -/
noncomputable def diskOne : PointedCGWH.{u, v} :=
  Under.mk
    ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (0 : Fin 2) :
          (Δ[0] : SSet.{v}) ⟶ Δ[1]))

/-- The ordered two-point boundary of the one-disk: the pointed summand maps
to `δ 0`, and the free summand maps to `δ 1`. -/
noncomputable def diskBoundary :
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ⟶
      diskOne.{u, v} :=
  Under.homMk
    (coprod.desc diskOne.{u, v}.hom
      ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        SSet.toCGWH.{u, v}.map
          (SSet.stdSimplex.δ (1 : Fin 2) :
            (Δ[0] : SSet.{v}) ⟶ Δ[1]))) (by
      simp [diskOne])

/-- Collapse the one-disk to the chosen terminal pointed CGWH object. -/
noncomputable def diskAugmentation :
    diskOne.{u, v} ⟶ ⊤_ PointedCGWH.{u, v} :=
  terminal.from _

/-- The ordinary pointed cofiber of the ordered boundary of the one-disk is
canonically the native one-sphere. -/
noncomputable def diskCofiberIsoSphereOne :
    (HomotopicalAlgebra.ordinaryCofiber
      (C := PointedCGWH.{u, v})).obj
        (Arrow.mk diskBoundary.{u, v}) ≅ sphereOne.{u, v} := by
  let S0 : PointedCGWH.{u, v} :=
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  let i := boundaryOneInclusion.{u, v}
  let c := boundaryOneCollapse.{u, v}
  let eBData := boundaryOneRealizationData.{u, v}
  let eB := eBData.1
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
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
  let hNative := IsPushout.of_hasPushout i c
  have hDisk : diskBoundary.{u, v}.right = d := by
    rfl
  have hBoundaryInv : eB.inv ≫ i = d := by
    apply Limits.coprod.hom_ext
    · calc
        _ = ((coprod.inl : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ eB.inv) ≫ i :=
          (Category.assoc _ _ _).symm
        _ = ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
              SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))) ≫ i := by
          rw [eBData.2.1]
        _ = p₀ := by
          change (e₀.inv ≫ SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (0 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι = p₀
          rw [Category.assoc, ← Functor.map_comp,
            SSet.boundary.ι_ι]
        _ = _ := (Limits.coprod.inl_desc p₀ p₁).symm
    · calc
        _ = ((coprod.inr : CGWH.point.{u, v} ⟶
              CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ eB.inv) ≫ i :=
          (Category.assoc _ _ _).symm
        _ = ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
              SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2))) ≫ i := by
          rw [eBData.2.2]
        _ = p₁ := by
          change (e₀.inv ≫ SSet.toCGWH.{u, v}.map
              (SSet.boundary.ι (1 : Fin 2))) ≫
            SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι = p₁
          rw [Category.assoc, ← Functor.map_comp,
            SSet.boundary.ι_ι]
        _ = _ := (Limits.coprod.inr_desc p₀ p₁).symm
  have hBoundary : i = eB.hom ≫ d := by
    rw [← hBoundaryInv, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  let q : diskOne.{u, v} ⟶ sphereOne.{u, v} :=
    Under.homMk (pushout.inl i c) (by
      change p₀ ≫ pushout.inl i c = pushout.inr i c
      rw [← Limits.coprod.inl_desc p₀ p₁]
      change (coprod.inl ≫ d) ≫ pushout.inl i c = _
      rw [← hBoundaryInv,
        Category.assoc, Category.assoc, hNative.w]
      have hp : ((coprod.inl : CGWH.point.{u, v} ⟶
          CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ eB.inv) ≫ c =
          𝟙 CGWH.point.{u, v} := by
        apply CGWH.point_isTerminal.hom_ext
      rw [← Category.assoc, ← Category.assoc, hp,
        Category.id_comp])
  let hT : IsTerminal ((⊤_ PointedCGWH.{u, v}).right) :=
    terminalIsTerminal.isTerminalObj
      (Under.forget CGWH.point.{u, v})
  let eT : (⊤_ PointedCGWH.{u, v}).right ≅ CGWH.point.{u, v} :=
    hT.uniqueUpToIso CGWH.point_isTerminal
  let z : (⊤_ PointedCGWH.{u, v}) ⟶ sphereOne.{u, v} :=
    Under.homMk (eT.hom ≫ pushout.inr i c) (by
      change (⊤_ PointedCGWH.{u, v}).hom ≫
          (eT.hom ≫ pushout.inr i c) = pushout.inr i c
      rw [← Category.assoc]
      have hp : (⊤_ PointedCGWH.{u, v}).hom ≫ eT.hom =
          𝟙 CGWH.point.{u, v} := by
        apply CGWH.point_isTerminal.hom_ext
      rw [hp, Category.id_comp])
  have hsq : diskBoundary.{u, v} ≫ q =
      terminal.from S0 ≫ z := by
    apply Under.UnderMorphism.ext
    change d ≫ pushout.inl i c =
      (terminal.from S0).right ≫ eT.hom ≫ pushout.inr i c
    rw [← hBoundaryInv, Category.assoc, hNative.w]
    exact congrArg (fun k => k ≫ pushout.inr i c)
      (CGWH.point_isTerminal.hom_ext
        (eB.inv ≫ c) ((terminal.from S0).right ≫ eT.hom))
  have hMappedD : IsPushout d
      (terminal.from S0).right q.right z.right := by
    apply hNative.of_iso eB (Iso.refl _) eT.symm (Iso.refl _)
    · exact hBoundary
    · apply hT.hom_ext
    · rfl
    · exact (eT.inv_hom_id_assoc _).symm
  have hMapped : IsPushout
      diskBoundary.{u, v}.right
      (terminal.from S0).right q.right z.right := by
    rw [hDisk]
    exact hMappedD
  have hUnder : IsPushout diskBoundary.{u, v}
      (terminal.from S0) q z :=
    IsPushout.of_map (Under.forget CGWH.point.{u, v}) hsq hMapped
  let hOrd := IsPushout.of_hasPushout diskBoundary.{u, v}
    (terminal.from S0)
  change pushout diskBoundary.{u, v} (terminal.from S0) ≅
    sphereOne.{u, v}
  exact hOrd.isoIsPushout _ _ hUnder

end PointedCGWH
