/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonFinite
public import
  Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import MathlibExt.Topology.Category.TopCat.ProdColimit

/-!
# Realization products with one finite simplicial factor

Let K be a simplicial set with finitely many nondegenerate simplices and Y any simplicial set.
The canonical map |K×Y|→|K|×|Y| is an isomorphism in TopCat, hence a homeomorphism.

The finite realization |K| is locally compact; expressing Y by its finite monogenous
subcomplexes permits passage from finite factors to arbitrary Y. Both factors lie in an
arbitrary universe u.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Simplicial MonoidalCategory

namespace SSet

/-- For a finite simplicial set K and arbitrary Y in SSet.{u}, the canonical geometric-realization
product comparison |K×Y|→|K|×|Y| is a topological isomorphism. -/
theorem isIso_prodComparison_toTop_finite_arbitrary
    (K Y : SSet.{u}) [K.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K Y) := by
  have ht : IsColimit Y.coconeN := Y.isColimitCoconeN
  have hpt : Y.coconeN.pt = Y := rfl
  have hFin : ∀ S : Y.N, SSet.Finite (Y.functorN.obj S) := fun S => by
    change SSet.Finite (S.subcomplex : SSet.{u})
    infer_instance
  have hStage : ∀ S : Y.N,
      IsIso (Limits.prodComparison SSet.toTop K (Y.functorN.obj S)) :=
    fun S => by
      have := hFin S
      exact SSet.isIso_prodComparison_toTop_finite_finite K _
  have : (Limits.prod.functor.obj K).IsLeftAdjoint :=
    CartesianMonoidalCategory.isLeftAdjoint_prod_functor K
  have htF : IsColimit
      ((Limits.prod.functor.obj K).mapCocone Y.coconeN) :=
    isColimitOfPreserves _ ht
  have htGF : IsColimit
      (SSet.toTop.mapCocone
        ((Limits.prod.functor.obj K).mapCocone Y.coconeN)) :=
    isColimitOfPreserves _ htF
  have htG : IsColimit (SSet.toTop.mapCocone Y.coconeN) :=
    isColimitOfPreserves _ ht
  have htHG : IsColimit
      ((Limits.prod.functor.obj (SSet.toTop.obj K)).mapCocone
        (SSet.toTop.mapCocone Y.coconeN)) :=
    isColimitOfPreserves _ htG
  have hSq : ∀ (S T : Y.N) (f : S ⟶ T),
      SSet.toTop.map
          ((Limits.prod.functor.obj K).map (Y.functorN.map f)) ≫
        Limits.prodComparison SSet.toTop K (Y.functorN.obj T) =
      Limits.prodComparison SSet.toTop K (Y.functorN.obj S) ≫
        (Limits.prod.functor.obj (SSet.toTop.obj K)).map
          (SSet.toTop.map (Y.functorN.map f)) := by
    intro S T f
    change SSet.toTop.map (Limits.prod.map (𝟙 K) _) ≫ _ =
      _ ≫ Limits.prod.map (𝟙 _) _
    simpa using Limits.prodComparison_natural (F := SSet.toTop) (𝟙 K)
      (Y.functorN.map f)
  have hY : Limits.prodComparison SSet.toTop K Y =
      Limits.prodComparison SSet.toTop K Y.coconeN.pt := by
    rfl
  have hSqLeg : ∀ S : Y.N,
      SSet.toTop.map
          ((Limits.prod.functor.obj K).map (Y.coconeN.ι.app S)) ≫
        Limits.prodComparison SSet.toTop K Y =
      Limits.prodComparison SSet.toTop K (Y.functorN.obj S) ≫
        (Limits.prod.functor.obj (SSet.toTop.obj K)).map
          (SSet.toTop.map (Y.coconeN.ι.app S)) := by
    intro S
    change SSet.toTop.map (Limits.prod.map (𝟙 K) _) ≫
        Limits.prodComparison SSet.toTop K Y.coconeN.pt =
      _ ≫ Limits.prod.map (𝟙 _) _
    simpa using Limits.prodComparison_natural (F := SSet.toTop) (𝟙 K)
      (Y.coconeN.ι.app S)
  let hα : (Y.functorN ⋙ Limits.prod.functor.obj K ⋙ SSet.toTop) ≅
      (Y.functorN ⋙ SSet.toTop ⋙
        Limits.prod.functor.obj (SSet.toTop.obj K)) :=
    NatIso.ofComponents
      (fun S => @CategoryTheory.asIso TopCat _ _ _
        (Limits.prodComparison SSet.toTop K (Y.functorN.obj S))
        (hStage S))
      (by intro S T f; exact hSq S T f)
  have hΦ : Limits.prodComparison SSet.toTop K Y =
      (IsColimit.coconePointsIsoOfNatIso htGF htHG hα).hom := by
    apply htGF.hom_ext
    intro S
    have hcomp :=
      IsColimit.comp_coconePointsIsoOfNatIso_hom htGF htHG hα S
    exact (hSqLeg S).trans hcomp.symm
  rw [hΦ]
  exact Iso.isIso_hom _

end SSet
