/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Original mapping fibres of a simplicial space

The endpoint map has source–target order `(d₁,d₀)`. Mapping fibres are the
actual chosen pullbacks over the Yoneda pair-points of the two original
vertices. Their maps retain prescribed target vertices and both projections.

These are raw data for Rezk2001 §5.1. No fibrancy, Segal or model assumption
is needed for the constructions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace

/-- The original map on outer-zero, inner-zero vertices. -/
abbrev mappingVertexMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (W.diagram _⦋0⦌) _⦋0⦌ → (V.diagram _⦋0⦌) _⦋0⦌ :=
  (f.hom.app (op ⦋0⦌)).app (op ⦋0⦌)

@[simp]
theorem mappingVertexMap_id (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) : mappingVertexMap (𝟙 W) x = x := rfl

@[simp]
theorem mappingVertexMap_comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingVertexMap (f ≫ g) x = mappingVertexMap g (mappingVertexMap f x) := rfl

/-- The original source–target endpoint map, with source `d₁` first. -/
def mappingEndpoint (W : SimplicialSpace.{u}) :
    W.diagram _⦋1⦌ ⟶ (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) :=
  prod.lift (W.diagram.δ 1) (W.diagram.δ 0)

@[reassoc (attr := simp)]
theorem mappingEndpoint_fst (W : SimplicialSpace.{u}) :
    mappingEndpoint W ≫ prod.fst = W.diagram.δ (1 : Fin 2) :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem mappingEndpoint_snd (W : SimplicialSpace.{u}) :
    mappingEndpoint W ≫ prod.snd = W.diagram.δ (0 : Fin 2) :=
  prod.lift_snd _ _

/-- Endpoint naturality keeps the original outer-one and outer-zero components. -/
@[reassoc]
theorem mappingEndpoint_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    mappingEndpoint W ≫ prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) =
      f.hom.app (op ⦋1⦌) ≫ mappingEndpoint V := by
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.map_fst, mappingEndpoint_fst,
      mappingEndpoint_fst_assoc] using SimplicialObject.δ_naturality f.hom (1 : Fin 2)
  · simpa only [Category.assoc, prod.map_snd, mappingEndpoint_snd,
      mappingEndpoint_snd_assoc] using SimplicialObject.δ_naturality f.hom (0 : Fin 2)

/-- The actual `Δ[0]` pair-point for the source vertex x and target vertex y. -/
def mappingPointPair (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) :=
  prod.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

@[reassoc (attr := simp)]
theorem mappingPointPair_fst (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingPointPair W x y ≫ prod.fst = SSet.yonedaEquiv.symm x :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem mappingPointPair_snd (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingPointPair W x y ≫ prod.snd = SSet.yonedaEquiv.symm y :=
  prod.lift_snd _ _

@[reassoc]
theorem mappingPointPair_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingPointPair W x y ≫ prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) =
      mappingPointPair V (mappingVertexMap f x) (mappingVertexMap f y) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, mappingPointPair_fst,
      mappingPointPair_fst_assoc, SSet.yonedaEquiv_symm_comp, mappingVertexMap]
  · simp only [Category.assoc, prod.map_snd, mappingPointPair_snd,
      mappingPointPair_snd_assoc, SSet.yonedaEquiv_symm_comp, mappingVertexMap]

/-- The chosen raw mapping fibre of the original `(d₁,d₀)` endpoint over `(x,y)`. -/
def mappingFibre (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (mappingEndpoint W) (mappingPointPair W x y)

namespace mappingFibre

/-- The original edge projection of the chosen pullback. -/
abbrev fst (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ W.diagram _⦋1⦌ :=
  pullback.fst (mappingEndpoint W) (mappingPointPair W x y)

/-- The original pair-point projection to `Δ[0]`. -/
abbrev snd (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd (mappingEndpoint W) (mappingPointPair W x y)

@[reassoc]
theorem condition (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    fst W x y ≫ mappingEndpoint W = snd W x y ≫ mappingPointPair W x y :=
  pullback.condition

/-- The fibre's source endpoint is the original source vertex. -/
@[reassoc (attr := simp)]
theorem source_eq (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    fst W x y ≫ W.diagram.δ (1 : Fin 2) = snd W x y ≫ SSet.yonedaEquiv.symm x := by
  have h := congrArg (fun k => k ≫ prod.fst) (condition W x y)
  simpa only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst] using h

/-- The fibre's target endpoint is the original target vertex. -/
@[reassoc (attr := simp)]
theorem target_eq (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    fst W x y ≫ W.diagram.δ (0 : Fin 2) = snd W x y ≫ SSet.yonedaEquiv.symm y := by
  have h := congrArg (fun k => k ≫ prod.snd) (condition W x y)
  simpa only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd] using h

/-- The induced whole fibre map, allowing explicitly prescribed target vertices. -/
def map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    mappingFibre W x y ⟶ mappingFibre V x' y' :=
  pullback.map (mappingEndpoint W) (mappingPointPair W x y)
    (mappingEndpoint V) (mappingPointPair V x' y')
    (f.hom.app (op ⦋1⦌)) (𝟙 _) (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))
    (mappingEndpoint_naturality f)
    (by rw [mappingPointPair_naturality, hx, hy, Category.id_comp])

@[reassoc (attr := simp)]
theorem map_fst {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    map f hx hy ≫ fst V x' y' = fst W x y ≫ f.hom.app (op ⦋1⦌) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    map f hx hy ≫ snd V x' y' = snd W x y := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[simp]
theorem map_id (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    map (𝟙 W) (x := x) (y := y) (x' := x) (y' := y) rfl rfl =
      𝟙 (mappingFibre W x y) := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W x y)
  · change map (𝟙 W) (x' := x) (y' := y) rfl rfl ≫ fst W x y =
      𝟙 (mappingFibre W x y) ≫ fst W x y
    rw [map_fst, Category.id_comp]
    exact Category.comp_id _
  · change map (𝟙 W) (x' := x) (y' := y) rfl rfl ≫ snd W x y =
      𝟙 (mappingFibre W x y) ≫ snd W x y
    rw [map_snd, Category.id_comp]

theorem map_comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    {x'' y'' : (U.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hx' : mappingVertexMap g x' = x'') (hy' : mappingVertexMap g y' = y'') :
    map f hx hy ≫ map g hx' hy' =
      map (f ≫ g) (x' := x'') (y' := y'') ((congrArg (mappingVertexMap g) hx).trans hx')
        ((congrArg (mappingVertexMap g) hy).trans hy') := by
  apply pullback.hom_ext (f := mappingEndpoint U) (g := mappingPointPair U x'' y'')
  · change (map f hx hy ≫ map g hx' hy') ≫ fst U x'' y'' =
      map (f ≫ g) (x' := x'') (y' := y'') ((congrArg (mappingVertexMap g) hx).trans hx')
        ((congrArg (mappingVertexMap g) hy).trans hy') ≫ fst U x'' y''
    simp only [Category.assoc, map_fst, map_fst_assoc]
    rfl
  · change (map f hx hy ≫ map g hx' hy') ≫ snd U x'' y'' =
      map (f ≫ g) (x' := x'') (y' := y'') ((congrArg (mappingVertexMap g) hx).trans hx')
        ((congrArg (mappingVertexMap g) hy).trans hy') ≫ snd U x'' y''
    simp only [Category.assoc, map_snd]

/-- A prescribed-vertex identity map is the native equality transport. -/
theorem map_id_eqToHom {W : SimplicialSpace.{u}}
    {x y x' y' : (W.diagram _⦋0⦌) _⦋0⦌} (hx : x = x') (hy : y = y') :
    map (𝟙 W) hx hy = eqToHom (by cases hx; cases hy; rfl) := by
  subst x'
  subst y'
  exact map_id W x y

/-- Prescribed target vertices use exactly the canonical map followed by native transport. -/
theorem map_eq_comp_eqToHom {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    map f hx hy =
      map f (x := x) (y := y) rfl rfl ≫ eqToHom (by cases hx; cases hy; rfl) := by
  cases hx
  cases hy
  exact (Category.comp_id _).symm

end mappingFibre

end SimplicialSpace
