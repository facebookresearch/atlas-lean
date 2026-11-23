/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

/-!
# Realization of a simplicial homotopy relative to a vertex

A simplicial homotopy which is stationary on a subcomplex containing a
chosen vertex realizes to a continuous homotopy relative to the singleton
containing that realized vertex.  The underlying ordinary continuous
homotopy is exactly `SSet.realizeHomotopy`, and its fixed value is the literal
realized target vertex `SSet.realizedVertex (f.app _ z)`.

The construction is universe-polymorphic and generic in the containing
subcomplex.  It makes no Waldhausen-specialized, pointed, loop-space,
additivity, weak-equivalence, spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
private theorem homotopyPrecomp_h_eq_fst_at_vertex
    {S : X.Subcomplex} (H : SSet.HomotopyRel f g S)
    (z : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (hz : z ∈ S.obj (Opposite.op (SimplexCategory.mk 0))) :
    (H.toHomotopy.precomp
      (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X)).h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u})
          (Δ[1] : SSet.{u}) ≫
        ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ f) := by
  let zS : (S : SSet.{u}).obj
      (Opposite.op (SimplexCategory.mk 0)) := ⟨z, hz⟩
  have hzS :
      (SSet.const zS : (Δ[0] : SSet.{u}) ⟶ (S : SSet.{u})) ≫ S.ι =
        (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) := by
    ext n x
    rfl
  rw [Homotopy.precomp_h]
  calc
    ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ▷
        (Δ[1] : SSet.{u})) ≫ H.h =
        (((SSet.const zS : (Δ[0] : SSet.{u}) ⟶ (S : SSet.{u})) ≫
          S.ι) ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
      rw [hzS]
    _ = ((SSet.const zS : (Δ[0] : SSet.{u}) ⟶ (S : SSet.{u})) ▷
          (Δ[1] : SSet.{u})) ≫
        ((S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h) := by
      rw [comp_whiskerRight_assoc]
    _ = ((SSet.const zS : (Δ[0] : SSet.{u}) ⟶ (S : SSet.{u})) ▷
          (Δ[1] : SSet.{u})) ≫
        (CartesianMonoidalCategory.fst (S : SSet.{u})
          (Δ[1] : SSet.{u}) ≫ S.ι ≫ f) := by
      rw [H.stationary_eq]
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{u})
          (Δ[1] : SSet.{u}) ≫
        ((SSet.const zS : (Δ[0] : SSet.{u}) ⟶ (S : SSet.{u})) ≫
          S.ι) ≫ f := by
      rw [CartesianMonoidalCategory.whiskerRight_fst_assoc]
      simp only [Category.assoc]
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{u})
          (Δ[1] : SSet.{u}) ≫
        ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ f) := by
      rw [hzS]

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing a stationary simplicial homotopy by its chosen vertex and
then realizing gives the constant-in-time map at the realized time-zero
value. -/
theorem realizeHomotopyMap_stationary_at_vertex
    {S : X.Subcomplex} (H : SSet.HomotopyRel f g S)
    (z : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (hz : z ∈ S.obj (Opposite.op (SimplexCategory.mk 0))) :
    Limits.prod.map (𝟙 TopCat.I.{u})
        (SSet.toTop.map
          (SSet.const z : (Δ[0] : SSet.{u}) ⟶ X)) ≫
        SSet.realizeHomotopyMap X Y f g H.toHomotopy =
      Limits.prod.snd ≫
        SSet.toTop.map
          ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ X) ≫ f) := by
  let k : (Δ[0] : SSet.{u}) ⟶ X := SSet.const z
  let R := H.toHomotopy.precomp k
  have hR : R.h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u})
        (Δ[1] : SSet.{u}) ≫ (k ≫ f) := by
    exact homotopyPrecomp_h_eq_fst_at_vertex H z hz
  calc
    Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H.toHomotopy =
      SSet.realizeHomotopyMap (Δ[0] : SSet.{u}) Y
        (k ≫ f) (k ≫ g) R := by
          exact realizeHomotopyMap_precomp H.toHomotopy k
    _ = Limits.prod.snd ≫ SSet.toTop.map (k ≫ f) := by
      exact realizeHomotopyMap_of_h_eq_fst R hR

/-- Realize a simplicial homotopy stationary at a chosen vertex as a
continuous homotopy relative to the singleton containing its realized
vertex. -/
noncomputable def realizeHomotopyRelAtVertex
    {S : X.Subcomplex} (H : SSet.HomotopyRel f g S)
    (z : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (hz : z ∈ S.obj (Opposite.op (SimplexCategory.mk 0))) :
    ContinuousMap.HomotopyRel
      (SSet.toTop.map f).hom (SSet.toTop.map g).hom
      {SSet.realizedVertex z} where
  toHomotopy := SSet.realizeHomotopy X Y f g H.toHomotopy
  prop' t x hx := by
    rw [Set.mem_singleton_iff.mp hx]
    let k : (Δ[0] : SSet.{u}) ⟶ X := SSet.const z
    let p0 := (TopCat.prodIsoProd TopCat.I
        (SSet.toTop.obj (Δ[0] : SSet.{u}))).inv
        (TopCat.I.homeomorph.symm t,
          (default : SSet.toTop.obj (Δ[0] : SSet.{u})))
    have hstat := realizeHomotopyMap_stationary_at_vertex H z hz
    change SSet.realizeHomotopyMap X Y f g H.toHomotopy
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm t, SSet.realizedVertex z)) =
      SSet.toTop.map f (SSet.realizedVertex z)
    have hk :
        SSet.toTop.map k
            (default : SSet.toTop.obj (Δ[0] : SSet.{u})) =
          SSet.realizedVertex z := by
      exact (SSet.realizedVertex_eq_const z).symm
    have hp :
        (Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k)) p0 =
          (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
            (TopCat.I.homeomorph.symm t, SSet.realizedVertex z) := by
      dsimp [p0]
      rw [TopCat.prodMap_prodIso_inv_apply, hk]
    rw [← hp]
    change
      (Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H.toHomotopy) p0 = _
    rw [hstat]
    change SSet.toTop.map (k ≫ f)
        ((Limits.prod.snd :
          TopCat.I.{u} ⨯ SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶
            SSet.toTop.obj (Δ[0] : SSet.{u})) p0) = _
    rw [TopCat.prodIsoProd_inv_snd_apply, Functor.map_comp]
    exact congrArg (SSet.toTop.map f) hk

/-- Forgetting fixed-vertex stationarity recovers the existing realized
ordinary homotopy definitionally. -/
@[simp]
theorem realizeHomotopyRelAtVertex_toHomotopy
    {S : X.Subcomplex} (H : SSet.HomotopyRel f g S)
    (z : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (hz : z ∈ S.obj (Opposite.op (SimplexCategory.mk 0))) :
    (realizeHomotopyRelAtVertex H z hz).toHomotopy =
      SSet.realizeHomotopy X Y f g H.toHomotopy :=
  rfl

/-- At every time, the realized relative homotopy fixes the chosen source
vertex at the literal realized image vertex. -/
@[simp]
theorem realizeHomotopyRelAtVertex_apply_basepoint
    {S : X.Subcomplex} (H : SSet.HomotopyRel f g S)
    (z : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (hz : z ∈ S.obj (Opposite.op (SimplexCategory.mk 0)))
    (t : unitInterval) :
    realizeHomotopyRelAtVertex H z hz
        (t, SSet.realizedVertex z) =
      SSet.realizedVertex (f.app _ z) := by
  rw [ContinuousMap.HomotopyRel.eq_fst _ t (by simp)]
  exact (SSet.realizedVertex_naturality f z).symm

end SSet
