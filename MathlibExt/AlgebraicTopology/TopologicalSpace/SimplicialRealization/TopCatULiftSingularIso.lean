/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Singular complexes under topological universe lift

The canonical singular-complex isomorphism retains each original
continuous simplex and is natural in every continuous source map.
This low-level module is shared by integral homology and topological
weak-equivalence transport.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace AlgebraicTopology.IntegralUniverseLift

private def singularSimplexEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X)).obj n ≃
      (TopCat.toSSet.obj X).obj n :=
  (TopCat.toSSetObjEquiv (TopCat.uliftFunctor.{v, u}.obj X) n).trans
    ((Homeomorph.refl _).continuousMapCongr
      (TopCat.uliftFunctorObjHomeo.{v, u} X).symm) |>.trans
        (TopCat.toSSetObjEquiv X n).symm

/-- Singular simplices in the lifted space are the actual lifted original
singular simplices, naturally in every simplicial degree. -/
public def singularSSetIso (X : TopCat.{u}) :
    TopCat.toSSet.obj (TopCat.uliftFunctor.{v, u}.obj X) ≅
      SSet.uliftFunctor.{v, u}.obj (TopCat.toSSet.obj X) :=
  NatIso.ofComponents (fun n =>
    Equiv.toIso ((singularSimplexEquiv.{u, v} X n).trans Equiv.ulift.symm))
    (by
      intro n m f
      ext σ
      apply ULift.down_injective
      apply (TopCat.toSSetObjEquiv X m).injective
      ext x
      rfl)

@[reassoc]
public theorem singularSSetIso_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.toSSet.map (TopCat.uliftFunctor.{v, u}.map f) ≫
      (singularSSetIso.{u, v} Y).hom =
    (singularSSetIso.{u, v} X).hom ≫
      SSet.uliftFunctor.{v, u}.map (TopCat.toSSet.map f) := by
  ext n σ
  apply ULift.down_injective
  apply (TopCat.toSSetObjEquiv Y n).injective
  ext x
  rfl

private theorem singularSSetIso_inv_app_computed (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (a : (TopCat.toSSet.obj X).obj n)
    (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquiv (TopCat.uliftFunctor.{v, u}.obj X) n
        ((singularSSetIso.{u, v} X).inv.app n (ULift.up a)) t =
      ULift.up (TopCat.toSSetObjEquiv X n a t) :=
  rfl

/-- The inverse canonical singular lift retains every original continuous
simplex value at every original simplex coordinate. -/
public theorem singularSSetIso_inv_app (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (a : (TopCat.toSSet.obj X).obj n)
    (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquiv (TopCat.uliftFunctor.{v, u}.obj X) n
        ((singularSSetIso.{u, v} X).inv.app n (ULift.up a)) t =
      ULift.up (TopCat.toSSetObjEquiv X n a t) :=
  singularSSetIso_inv_app_computed X n a t

private theorem singularSSetIso_inv_point_computed (X : TopCat.{u}) (x : X) :
    (singularSSetIso.{u, v} X).inv.app (op ⦋0⦌) (ULift.up (TopCat.toSSetObj₀Equiv.symm x)) =
      TopCat.toSSetObj₀Equiv.symm (ULift.up x) := by
  apply (TopCat.toSSetObjEquiv (TopCat.uliftFunctor.{v, u}.obj X) (op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro t
  rfl

/-- The inverse canonical singular lift preserves the actual original marked vertex. -/
public theorem singularSSetIso_inv_point (X : TopCat.{u}) (x : X) :
    (singularSSetIso.{u, v} X).inv.app (op ⦋0⦌) (ULift.up (TopCat.toSSetObj₀Equiv.symm x)) =
      TopCat.toSSetObj₀Equiv.symm (ULift.up x) :=
  singularSSetIso_inv_point_computed X x

/-- The whole original source-map square retains the inverse canonical singular lift. -/
@[reassoc]
public theorem singularSSetIso_inv_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.uliftFunctor.{v, u}.map (TopCat.toSSet.map f) ≫ (singularSSetIso.{u, v} Y).inv =
      (singularSSetIso.{u, v} X).inv ≫ TopCat.toSSet.map (TopCat.uliftFunctor.{v, u}.map f) := by
  apply (cancel_epi (singularSSetIso.{u, v} X).hom).mp
  rw [← Category.assoc, ← singularSSetIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end AlgebraicTopology.IntegralUniverseLift
