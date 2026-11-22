/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFixedEdgeNaturality
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Actual original coherent edge lifts without locally Kan targets

A genuine full original Hom boundary right class is surjective on
original Hom vertices. The existing complete fixed-edge equivalence
then lifts the SAME original coherent edge between its prescribed
individual objects, including its entire enriched-functor value.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalCoherentEdgeLifting
open SimplicialEnrichment HomMappingCells

/-- The actual full boundary right class is surjective on individual original scalar vertices. -/
theorem hom_vertices_surjective {A B : SSet.{u}} (p : A ⟶ B)
    (hp : SSet.modelCategoryQuillen.I.rlp p) :
    Function.Surjective (p.app (op ⦋0⦌)) := by
  intro y
  let hinit : IsInitial (∂Δ[0] : SSet.{u}) :=
    (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
      (SSet.Subcomplex.eqToIso SSet.boundary_zero).symm
  let _ : HasLiftingProperty (SSet.boundary.{u} 0).ι p :=
    hp _ (SSet.modelCategoryQuillen.boundary_ι_mem_I 0)
  let sq : CommSq (hinit.to A) (SSet.boundary.{u} 0).ι p (SSet.yonedaEquiv.symm y) :=
    ⟨hinit.hom_ext _ _⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  exact (SSet.yonedaEquiv_comp sq.lift p).symm.trans
    ((congrArg SSet.yonedaEquiv sq.fac_right).trans (Equiv.apply_symm_apply _ _))

/-- A prescribed whole original fixed edge lifts under the actual original Hom vertex-surjectivity hypothesis. -/
theorem exists_fixed_edge_lift {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)
    (hHom : Function.Surjective ((F.map x y).app (op ⦋0⦌)))
    (σ : FixedSimplex (F.obj x) (F.obj y) (n := 0)) :
    ∃ τ : FixedSimplex x y (n := 0), τ.val ≫ F = σ.val := by
  obtain ⟨a,ha⟩ := hHom (FixedEdgeReadback.readVertex (F.obj x) (F.obj y) σ)
  refine ⟨construct x y a, ?_⟩
  have h := (OriginalFixedEdgeNaturality.construct_postcompose F x y a).trans
    ((congrArg (construct (F.obj x) (F.obj y)) ha).trans
      (FixedEdgeReadback.construct_read (F.obj x) (F.obj y) σ))
  exact congrArg Subtype.val h

/-- Genuine full original Hom boundary lifting supplies the entire same coherent edge lift. -/
theorem exists_fixed_edge_lift_of_hom_boundaries {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)
    (hHom : SSet.modelCategoryQuillen.I.rlp (F.map x y))
    (σ : FixedSimplex (F.obj x) (F.obj y) (n := 0)) :
    ∃ τ : FixedSimplex x y (n := 0), τ.val ≫ F = σ.val :=
  exists_fixed_edge_lift F x y (hom_vertices_surjective (F.map x y) hHom) σ

/-- The original target edge with its true prescribed endpoint-image equalities. -/
def fixedTarget {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)
    (σ : coherentSimplex.{u} ⦋1⦌ ⟶ D)
    (hx : F.obj x = σ.obj (.mk (ULift.up (0 : Fin 2))))
    (hy : F.obj y = σ.obj (.mk (ULift.up (Fin.last 1)))) :
    FixedSimplex (F.obj x) (F.obj y) (n := 0) := ⟨σ, hx.symm, hy.symm⟩

/-- The same entire prescribed target enriched edge is retained by the endpoint typing. -/
theorem fixedTarget_val {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)
    (σ : coherentSimplex.{u} ⦋1⦌ ⟶ D)
    (hx : F.obj x = σ.obj (.mk (ULift.up (0 : Fin 2))))
    (hy : F.obj y = σ.obj (.mk (ULift.up (Fin.last 1)))) :
    (fixedTarget F x y σ hx hy).val = σ := rfl

end CategoryTheory.CoherentRealization.OriginalCoherentEdgeLifting
