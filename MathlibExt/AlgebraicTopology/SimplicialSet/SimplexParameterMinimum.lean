/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Hom.Order
public import Mathlib.Order.MinMax
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import MathlibExt.CategoryTheory.NerveHomotopy

/-! # Canonical simplex parameter minimum

This shared implementation retains both original simplex coordinates and
supplies the interval minimum and the relative parameter prism.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.ParameterComparison

variable {L m q : SimplexCategory}

/-- The finite product order uses its canonical preorder category throughout these comparisons. -/
local instance parameterOrderCategory (L q : SimplexCategory) :
    SmallCategory (Fin (L.len + 1) × Fin (q.len + 1)) := Preorder.smallCategory _

/-- The unchanged first coordinate of the original coefficient domain. -/
def sourceCoordinate (τ : L ⟶ m) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) :=
  τ.toOrderHom.comp OrderHom.fst

/-- The entire scalar parameter retained through the domain coordinate. -/
def domainCoordinate (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) :=
  ρ.toOrderHom.comp OrderHom.fst

/-- The independent external scalar coordinate. -/
def externalCoordinate :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) := OrderHom.snd

/-- The canonical pointwise infimum of both full scalar coordinates. -/
def minimumCoordinate (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) :=
  domainCoordinate ρ ⊓ externalCoordinate

/-- Pull back the original domain while keeping the external scalar parameter. -/
def pullbackCoordinates (τ : L ⟶ m) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod externalCoordinate

/-- Retain the entire scalar family through its domain parameter. -/
def domainCoordinates (τ : L ⟶ m) (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod (domainCoordinate ρ)

/-- The common lower family retains the same first coordinate. -/
def minimumCoordinates (τ : L ⟶ m) (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod (minimumCoordinate ρ)

/-- Both complete coordinates of the pulled family are read literally. -/
theorem pullbackCoordinates_apply (τ : L ⟶ m)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    pullbackCoordinates τ p = (τ.toOrderHom p.1, p.2) := rfl

/-- Both complete coordinates of the domain family are read literally. -/
theorem domainCoordinates_apply (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    domainCoordinates τ ρ p = (τ.toOrderHom p.1, ρ.toOrderHom p.1) := rfl

/-- The common family uses the actual finite-order minimum. -/
theorem minimumCoordinates_apply (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    minimumCoordinates τ ρ p = (τ.toOrderHom p.1, min (ρ.toOrderHom p.1) p.2) := rfl

/-- The common family lies below the domain family in the actual product order. -/
theorem minimum_le_domain (τ : L ⟶ m) (ρ : L ⟶ q) :
    minimumCoordinates τ ρ ≤ domainCoordinates τ ρ :=
  OrderHom.prod_mono le_rfl inf_le_left

/-- The common family lies below the pulled family in the actual product order. -/
theorem minimum_le_pullback (τ : L ⟶ m) (ρ : L ⟶ q) :
    minimumCoordinates τ ρ ≤ pullbackCoordinates τ :=
  OrderHom.prod_mono le_rfl inf_le_right

/-- The canonical order-functor comparison to the complete domain family. -/
def minimumToDomain (τ : L ⟶ m) (ρ : L ⟶ q) :
    (minimumCoordinates τ ρ).toFunctor ⟶ (domainCoordinates τ ρ).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map (homOfLE (minimum_le_domain τ ρ))

/-- The canonical order-functor comparison to the complete pulled family. -/
def minimumToPullback (τ : L ⟶ m) (ρ : L ⟶ q) :
    (minimumCoordinates τ ρ).toFunctor ⟶ (pullbackCoordinates τ).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map (homOfLE (minimum_le_pullback τ ρ))

/-- Every comparison component is the original pointwise product-order arrow. -/
theorem minimumToDomain_app (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    (minimumToDomain τ ρ).app p = homOfLE (minimum_le_domain τ ρ p) := rfl

/-- Every pulled comparison component is the original pointwise product-order arrow. -/
theorem minimumToPullback_app (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    (minimumToPullback τ ρ).app p = homOfLE (minimum_le_pullback τ ρ p) := rfl

/-- A real split scalar graph makes the entire common family equal to the pulled family there. -/
theorem minimumCoordinates_graph (τ : L ⟶ m) (ρ : L ⟶ q)
    (κ : q ⟶ L) (hκ : κ ≫ ρ = 𝟙 q) (k : Fin (q.len + 1)) :
    minimumCoordinates τ ρ (κ.toOrderHom k, k) =
      pullbackCoordinates τ (κ.toOrderHom k, k) := by
  have hk : ρ.toOrderHom (κ.toOrderHom k) = k :=
    congr_toOrderHom_apply hκ k
  change (τ.toOrderHom (κ.toOrderHom k), min (ρ.toOrderHom (κ.toOrderHom k)) k) = _
  rw [hk, min_self]
  rfl

/-- The same split graph identifies the entire domain family with the pulled family. -/
theorem domainCoordinates_graph (τ : L ⟶ m) (ρ : L ⟶ q)
    (κ : q ⟶ L) (hκ : κ ≫ ρ = 𝟙 q) (k : Fin (q.len + 1)) :
    domainCoordinates τ ρ (κ.toOrderHom k, k) =
      pullbackCoordinates τ (κ.toOrderHom k, k) := by
  exact congrArg (fun r => (τ.toOrderHom (κ.toOrderHom k), r))
    (congr_toOrderHom_apply hκ k)

variable {L' m' q' : SimplexCategory}

/-- The full pulled coordinates respect every actual commuting source square. -/
theorem pullbackCoordinates_naturality (τ : L ⟶ m) (τ' : L' ⟶ m')
    (δ : L' ⟶ L) (γ : m' ⟶ m) (α : q' ⟶ q) (hτ : δ ≫ τ = τ' ≫ γ) :
    (pullbackCoordinates (q := q) τ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) =
      (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (pullbackCoordinates τ') := by
  apply OrderHom.ext
  funext p
  apply Prod.ext
  · exact congr_toOrderHom_apply hτ p.1
  · rfl

/-- The entire domain scalar coordinates respect both actual commuting squares. -/
theorem domainCoordinates_naturality (τ : L ⟶ m) (ρ : L ⟶ q)
    (τ' : L' ⟶ m') (ρ' : L' ⟶ q') (δ : L' ⟶ L) (γ : m' ⟶ m) (α : q' ⟶ q)
    (hτ : δ ≫ τ = τ' ≫ γ) (hρ : δ ≫ ρ = ρ' ≫ α) :
    (domainCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) =
      (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (domainCoordinates τ' ρ') := by
  apply OrderHom.ext
  funext p
  apply Prod.ext
  · exact congr_toOrderHom_apply hτ p.1
  · exact congr_toOrderHom_apply hρ p.1

/-- Minimum comparison is natural for every scalar operator, including noninjective ones. -/
theorem minimumCoordinates_naturality (τ : L ⟶ m) (ρ : L ⟶ q)
    (τ' : L' ⟶ m') (ρ' : L' ⟶ q') (δ : L' ⟶ L) (γ : m' ⟶ m) (α : q' ⟶ q)
    (hτ : δ ≫ τ = τ' ≫ γ) (hρ : δ ≫ ρ = ρ' ≫ α) :
    (minimumCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) =
      (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (minimumCoordinates τ' ρ') := by
  apply OrderHom.ext
  funext p
  apply Prod.ext
  · exact congr_toOrderHom_apply hτ p.1
  · change min (ρ.toOrderHom (δ.toOrderHom p.1)) (α.toOrderHom p.2) =
      α.toOrderHom (min (ρ'.toOrderHom p.1) p.2)
    have hr : ρ.toOrderHom (δ.toOrderHom p.1) = α.toOrderHom (ρ'.toOrderHom p.1) :=
      congr_toOrderHom_apply hρ p.1
    rw [hr]
    exact (α.toOrderHom.monotone.map_min).symm

end SimplexCategory.ParameterComparison

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SimplexCategory.ParameterComparison

namespace SSet.SimplexParameterComparison

/-- Lift an order map to the same universe used by the simplex nerve coordinates. -/
def liftedCoordinates {X Y : Type} [Preorder X] [Preorder Y] (f : X →o Y) :
    ULift.{u} X →o ULift.{u} Y :=
  (ULift.orderIso.symm.toOrderEmbedding.toOrderHom).comp
    (f.comp ULift.orderIso.toOrderEmbedding.toOrderHom)

/-- The product-simplex map induced by the supplied monotone coordinate map. -/
def coordinateMap {p q r s : SimplexCategory}
    (f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1)) :
    stdSimplex.obj p ⊗ stdSimplex.obj q ⟶ stdSimplex.obj r ⊗ stdSimplex.obj s :=
  ((prodStdSimplex.isoNerve.{u} p.len q.len).hom ≫
    nerveMap (liftedCoordinates.{u} f).toFunctor) ≫
      (prodStdSimplex.isoNerve.{u} r.len s.len).inv

/-- Lifting preserves the exact original value of each coordinate. -/
@[simp]
theorem liftedCoordinates_apply {X Y : Type} [Preorder X] [Preorder Y]
    (f : X →o Y) (x : ULift.{u} X) : liftedCoordinates f x = ULift.up (f x.down) := rfl

/-- Every simplex vertex is sent to the supplied pair of original coordinates. -/
theorem coordinateMap_apply {p q r s : SimplexCategory}
    (f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1))
    (a : SimplexCategoryᵒᵖ) (z : (stdSimplex.obj p ⊗ stdSimplex.obj q).obj a)
    (i : Fin (a.unop.len + 1)) :
    (stdSimplex.asOrderHom ((coordinateMap f).app a z).1 i,
      stdSimplex.asOrderHom ((coordinateMap f).app a z).2 i) =
        f (stdSimplex.asOrderHom z.1 i, stdSimplex.asOrderHom z.2 i) := rfl

variable {L m q : SimplexCategory}

/-- The original domain is pulled back with its entire external scalar coordinate. -/
def pullbackMap (τ : L ⟶ m) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (pullbackCoordinates τ)

/-- The scalar coordinate is retained through the complete domain parameter. -/
def domainMap (τ : L ⟶ m) (ρ : L ⟶ q) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (domainCoordinates τ ρ)

/-- The common lower family uses the minimum of the two entire scalar coordinates. -/
def minimumMap (τ : L ⟶ m) (ρ : L ⟶ q) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (minimumCoordinates τ ρ)

/-- The pulled map retains both actual simplex coordinates in every degree. -/
theorem pullbackMap_apply (τ : L ⟶ m) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    (pullbackMap τ).app a p = ((stdSimplex.map τ).app a p.1, p.2) := by
  apply Prod.ext
  · rfl
  · exact stdSimplex.ext _ _ (fun _ => rfl)

/-- The nerve presentation is exactly the original tensor whiskering of the domain map. -/
theorem pullbackMap_eq_whiskerRight (τ : L ⟶ m) :
    pullbackMap (q := q) τ = SSet.stdSimplex.map τ ▷ SSet.stdSimplex.obj q := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro p
  exact pullbackMap_apply τ a p

/-- Every coordinate of the complete domain family reads its original ordinal. -/
theorem domainMap_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    (domainMap τ ρ).app a p =
      ((stdSimplex.map τ).app a p.1, (stdSimplex.map ρ).app a p.1) := rfl

/-- The first coordinate is unchanged by the minimum interpolation. -/
theorem minimumMap_fst_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    ((minimumMap τ ρ).app a p).1 = (stdSimplex.map τ).app a p.1 := rfl

/-- The second coordinate is the pointwise minimum of the original scalar parameters. -/
theorem minimumMap_snd_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) (i : Fin (a.unop.len + 1)) :
    stdSimplex.asOrderHom (((minimumMap τ ρ).app a p).2) i =
      min (ρ.toOrderHom (stdSimplex.asOrderHom p.1 i)) (stdSimplex.asOrderHom p.2 i) := rfl

/-- Coordinate maps commute with every supplied domain and scalar operator square. -/
theorem coordinateMap_naturality {L' m' q' : SimplexCategory}
    (f : Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1))
    (f' : Fin (L'.len + 1) × Fin (q'.len + 1) →o Fin (m'.len + 1) × Fin (q'.len + 1))
    (δ : L' ⟶ L) (γ : m' ⟶ m) (α : q' ⟶ q)
    (h : f.comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) =
      (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp f') :
    (stdSimplex.map δ ⊗ₘ stdSimplex.map α) ≫ coordinateMap.{u} f =
      coordinateMap.{u} f' ≫ (stdSimplex.map γ ⊗ₘ stdSimplex.map α) := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro p
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    exact congrArg Prod.fst (congrArg (fun k => k
      (stdSimplex.asOrderHom p.1 i, stdSimplex.asOrderHom p.2 i)) h)
  · apply stdSimplex.ext
    intro i
    exact congrArg Prod.snd (congrArg (fun k => k
      (stdSimplex.asOrderHom p.1 i, stdSimplex.asOrderHom p.2 i)) h)

end SSet.SimplexParameterComparison
