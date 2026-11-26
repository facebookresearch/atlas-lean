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

/-!
# Minimum comparison of simplex parameters

Let `L, m, q : SimplexCategory`, with ordinal maps `τ : L ⟶ m` and `ρ : L ⟶ q`. On the product of finite ordinals `Fin (L.len + 1) × Fin (q.len + 1)`, compare the monotone maps
`(x, k) ↦ (τ(x), k)`, `(x, k) ↦ (τ(x), ρ(x))`, and `(x, k) ↦ (τ(x), min (ρ(x), k))`.
The third map is pointwise below the first two and hence gives natural transformations between their preorder functors. If `κ : q ⟶ L` satisfies `κ ≫ ρ = 𝟙 q`, all three maps agree on `(κ(k), k)`.

These coordinate maps respect commuting diagrams of ordinal maps, including maps of the
parameter ordinal `q`. Via nerves of product ordinals, every monotone coordinate map gives a
simplicial map between products of standard simplices in universe `u`. The induced pullback
map is tensor whiskering by `stdSimplex.obj q`; the domain and minimum maps have the
corresponding pointwise simplex-coordinate formulas.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.ParameterComparison

variable {L m q : SimplexCategory}

/-- For `L, q : SimplexCategory`, the category on `Fin (L.len + 1) × Fin (q.len + 1)` induced by
its componentwise order. There is a morphism from `(x, k)` to `(y, l)` exactly when `x ≤ y`
and `k ≤ l`, and such a morphism is unique. -/
local instance parameterOrderCategory (L q : SimplexCategory) :
    SmallCategory (Fin (L.len + 1) × Fin (q.len + 1)) := Preorder.smallCategory _

/-- For `L, m, q : SimplexCategory` and `τ : L ⟶ m`, the monotone map from `Fin (L.len + 1) × Fin
(q.len + 1)` to `Fin (m.len + 1)` sending `(x, k)` to `τ.toOrderHom x`. -/
def sourceCoordinate (τ : L ⟶ m) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) :=
  τ.toOrderHom.comp OrderHom.fst

/-- For `L, q : SimplexCategory` and `ρ : L ⟶ q`, the monotone map from `Fin (L.len + 1) × Fin
(q.len + 1)` to `Fin (q.len + 1)` sending `(x, k)` to `ρ.toOrderHom x`. Its value depends only
on the source-ordinal coordinate. -/
def domainCoordinate (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) :=
  ρ.toOrderHom.comp OrderHom.fst

/-- For `L, q : SimplexCategory`, the second projection `Fin (L.len + 1) × Fin (q.len + 1) →o Fin
(q.len + 1)`, sending `(x, k)` to `k`. -/
def externalCoordinate :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) := OrderHom.snd

/-- For `L, q : SimplexCategory` and `ρ : L ⟶ q`, the monotone map from `Fin (L.len + 1) × Fin
(q.len + 1)` to `Fin (q.len + 1)` given by `(x, k) ↦ min (ρ.toOrderHom x) k`. It is the
pointwise infimum of `domainCoordinate ρ` and `externalCoordinate`. -/
def minimumCoordinate (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (q.len + 1) :=
  domainCoordinate ρ ⊓ externalCoordinate

/-- For `L, m, q : SimplexCategory` and `τ : L ⟶ m`, the monotone map `Fin (L.len + 1) × Fin
(q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1)` given by `(x, k) ↦ (τ.toOrderHom x, k)`. -/
def pullbackCoordinates (τ : L ⟶ m) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod externalCoordinate

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the monotone map `Fin (L.len +
1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1)` given by `(x, k) ↦ (τ.toOrderHom x,
ρ.toOrderHom x)`. -/
def domainCoordinates (τ : L ⟶ m) (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod (domainCoordinate ρ)

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the monotone map from `Fin
(L.len + 1) × Fin (q.len + 1)` to `Fin (m.len + 1) × Fin (q.len + 1)` sending `(x, k)` to
`(τ.toOrderHom x, min (ρ.toOrderHom x) k)`. -/
def minimumCoordinates (τ : L ⟶ m) (ρ : L ⟶ q) :
    Fin (L.len + 1) × Fin (q.len + 1) →o Fin (m.len + 1) × Fin (q.len + 1) :=
  (sourceCoordinate τ).prod (minimumCoordinate ρ)

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`pullbackCoordinates τ p = (τ.toOrderHom p.1, p.2)`. -/
theorem pullbackCoordinates_apply (τ : L ⟶ m)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    pullbackCoordinates τ p = (τ.toOrderHom p.1, p.2) := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`domainCoordinates τ ρ p = (τ.toOrderHom p.1, ρ.toOrderHom p.1)`. -/
theorem domainCoordinates_apply (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    domainCoordinates τ ρ p = (τ.toOrderHom p.1, ρ.toOrderHom p.1) := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`minimumCoordinates τ ρ p = (τ.toOrderHom p.1, min (ρ.toOrderHom p.1) p.2)`. -/
theorem minimumCoordinates_apply (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    minimumCoordinates τ ρ p = (τ.toOrderHom p.1, min (ρ.toOrderHom p.1) p.2) := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`,
`minimumCoordinates τ ρ ≤ domainCoordinates τ ρ`
in the pointwise order on maps between the finite product ordinals. At `(x, k)`, the first coordinates are equal and `min (ρ(x), k) ≤ ρ(x)`. -/
theorem minimum_le_domain (τ : L ⟶ m) (ρ : L ⟶ q) :
    minimumCoordinates τ ρ ≤ domainCoordinates τ ρ :=
  OrderHom.prod_mono le_rfl inf_le_left

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`,
`minimumCoordinates τ ρ ≤ pullbackCoordinates τ`
in the pointwise order on maps between the finite product ordinals. At `(x, k)`, the first coordinates are equal and `min (ρ(x), k) ≤ k`. -/
theorem minimum_le_pullback (τ : L ⟶ m) (ρ : L ⟶ q) :
    minimumCoordinates τ ρ ≤ pullbackCoordinates τ :=
  OrderHom.prod_mono le_rfl inf_le_right

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the natural transformation
`(minimumCoordinates τ ρ).toFunctor ⟶ (domainCoordinates τ ρ).toFunctor` induced by the
pointwise inequality. Its component at `(x, k)` is the unique preorder arrow from `(τ(x), min
(ρ(x), k))` to `(τ(x), ρ(x))`. -/
def minimumToDomain (τ : L ⟶ m) (ρ : L ⟶ q) :
    (minimumCoordinates τ ρ).toFunctor ⟶ (domainCoordinates τ ρ).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map (homOfLE (minimum_le_domain τ ρ))

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the natural transformation
`(minimumCoordinates τ ρ).toFunctor ⟶ (pullbackCoordinates τ).toFunctor` induced by the
pointwise inequality. At `(x, k)`, its component is the unique preorder arrow from `(τ(x), min
(ρ(x), k))` to `(τ(x), k)`. -/
def minimumToPullback (τ : L ⟶ m) (ρ : L ⟶ q) :
    (minimumCoordinates τ ρ).toFunctor ⟶ (pullbackCoordinates τ).toFunctor :=
  OrderHom.equivalenceFunctor.functor.map (homOfLE (minimum_le_pullback τ ρ))

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`(minimumToDomain τ ρ).app p = homOfLE (minimum_le_domain τ ρ p)`.
The component is the unique arrow in the componentwise preorder category from the minimum coordinates to the source-parameter coordinates. -/
theorem minimumToDomain_app (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    (minimumToDomain τ ρ).app p = homOfLE (minimum_le_domain τ ρ p) := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `p : Fin (L.len + 1) × Fin (q.len + 1)`,
`(minimumToPullback τ ρ).app p = homOfLE (minimum_le_pullback τ ρ p)`.
This is the unique preorder arrow from the minimum coordinates to the coordinates with external parameter `p.2`. -/
theorem minimumToPullback_app (τ : L ⟶ m) (ρ : L ⟶ q)
    (p : Fin (L.len + 1) × Fin (q.len + 1)) :
    (minimumToPullback τ ρ).app p = homOfLE (minimum_le_pullback τ ρ p) := rfl

/-- Let `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `κ : q ⟶ L` satisfy `κ ≫ ρ = 𝟙 q`. For every `k : Fin (q.len + 1)`,
`minimumCoordinates τ ρ (κ.toOrderHom k, k) = pullbackCoordinates τ (κ.toOrderHom k, k)`.
On this graph, `ρ(κ(k)) = k`, so the minimum parameter equals `k`. -/
theorem minimumCoordinates_graph (τ : L ⟶ m) (ρ : L ⟶ q)
    (κ : q ⟶ L) (hκ : κ ≫ ρ = 𝟙 q) (k : Fin (q.len + 1)) :
    minimumCoordinates τ ρ (κ.toOrderHom k, k) =
      pullbackCoordinates τ (κ.toOrderHom k, k) := by
  have hk : ρ.toOrderHom (κ.toOrderHom k) = k :=
    congr_toOrderHom_apply hκ k
  change (τ.toOrderHom (κ.toOrderHom k), min (ρ.toOrderHom (κ.toOrderHom k)) k) = _
  rw [hk, min_self]
  rfl

/-- Let `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, and `κ : q ⟶ L` satisfy `κ ≫ ρ = 𝟙 q`. For every `k : Fin (q.len + 1)`,
`domainCoordinates τ ρ (κ.toOrderHom k, k) = pullbackCoordinates τ (κ.toOrderHom k, k)`.
The two parameter coordinates agree because `ρ(κ(k)) = k`. -/
theorem domainCoordinates_graph (τ : L ⟶ m) (ρ : L ⟶ q)
    (κ : q ⟶ L) (hκ : κ ≫ ρ = 𝟙 q) (k : Fin (q.len + 1)) :
    domainCoordinates τ ρ (κ.toOrderHom k, k) =
      pullbackCoordinates τ (κ.toOrderHom k, k) := by
  exact congrArg (fun r => (τ.toOrderHom (κ.toOrderHom k), r))
    (congr_toOrderHom_apply hκ k)

variable {L' m' q' : SimplexCategory}

/-- For ordinal maps `τ : L ⟶ m`, `τ' : L' ⟶ m'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q` in `SimplexCategory`, suppose `δ ≫ τ = τ' ≫ γ`. Then
`(pullbackCoordinates (q := q) τ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (pullbackCoordinates τ')`.
Thus changing the source and parameter ordinals commutes with applying `τ` to the first coordinate. -/
theorem pullbackCoordinates_naturality (τ : L ⟶ m) (τ' : L' ⟶ m')
    (δ : L' ⟶ L) (γ : m' ⟶ m) (α : q' ⟶ q) (hτ : δ ≫ τ = τ' ≫ γ) :
    (pullbackCoordinates (q := q) τ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) =
      (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (pullbackCoordinates τ') := by
  apply OrderHom.ext
  funext p
  apply Prod.ext
  · exact congr_toOrderHom_apply hτ p.1
  · rfl

/-- For ordinal maps `τ : L ⟶ m`, `ρ : L ⟶ q`, `τ' : L' ⟶ m'`, `ρ' : L' ⟶ q'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, suppose `δ ≫ τ = τ' ≫ γ` and `δ ≫ ρ = ρ' ≫ α`. Then
`(domainCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (domainCoordinates τ' ρ')`.
This is an equality of monotone maps between the indicated finite product ordinals. -/
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

/-- For ordinal maps `τ : L ⟶ m`, `ρ : L ⟶ q`, `τ' : L' ⟶ m'`, `ρ' : L' ⟶ q'`, `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, suppose `δ ≫ τ = τ' ≫ γ` and `δ ≫ ρ = ρ' ≫ α`. Then
`(minimumCoordinates τ ρ).comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp (minimumCoordinates τ' ρ')`.
The parameter map `α` may be noninjective; monotone maps of finite linear orders preserve minima. -/
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

/-- For preorders `X, Y : Type` and a monotone map `f : X →o Y`, the monotone map
`liftedCoordinates.{u} f : ULift.{u} X →o ULift.{u} Y` transports `f` through the order
isomorphisms with `X` and `Y`. It sends `x` to `ULift.up (f x.down)`. -/
def liftedCoordinates {X Y : Type} [Preorder X] [Preorder Y] (f : X →o Y) :
    ULift.{u} X →o ULift.{u} Y :=
  (ULift.orderIso.symm.toOrderEmbedding.toOrderHom).comp
    (f.comp ULift.orderIso.toOrderEmbedding.toOrderHom)

/-- For `p, q, r, s : SimplexCategory` and a monotone map `f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1)`, the induced simplicial map in universe `u` is
`stdSimplex.obj p ⊗ stdSimplex.obj q ⟶ stdSimplex.obj r ⊗ stdSimplex.obj s`.
It is the nerve of the lifted preorder functor of `f`, transported through the isomorphisms identifying products of standard simplices with nerves of product ordinals. -/
def coordinateMap {p q r s : SimplexCategory}
    (f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1)) :
    stdSimplex.obj p ⊗ stdSimplex.obj q ⟶ stdSimplex.obj r ⊗ stdSimplex.obj s :=
  ((prodStdSimplex.isoNerve.{u} p.len q.len).hom ≫
    nerveMap (liftedCoordinates.{u} f).toFunctor) ≫
      (prodStdSimplex.isoNerve.{u} r.len s.len).inv

/-- For preorders `X, Y : Type`, `f : X →o Y`, and `x : ULift.{u} X`,
`liftedCoordinates f x = ULift.up (f x.down)`. -/
@[simp]
theorem liftedCoordinates_apply {X Y : Type} [Preorder X] [Preorder Y]
    (f : X →o Y) (x : ULift.{u} X) : liftedCoordinates f x = ULift.up (f x.down) := rfl

/-- Let `f` be a monotone map from the product of the finite ordinals of `p, q : SimplexCategory` to that of `r, s`. For `a : SimplexCategoryᵒᵖ`, a simplex `z` of `stdSimplex.obj p ⊗ stdSimplex.obj q : SSet.{u}` in degree `a`, and `i : Fin (a.unop.len + 1)`,
`(asOrderHom ((coordinateMap f).app a z).1 i, asOrderHom ((coordinateMap f).app a z).2 i) = f (asOrderHom z.1 i, asOrderHom z.2 i)`.
Here `asOrderHom` denotes the monotone-coordinate description of a standard-simplex simplex. -/
theorem coordinateMap_apply {p q r s : SimplexCategory}
    (f : Fin (p.len + 1) × Fin (q.len + 1) →o Fin (r.len + 1) × Fin (s.len + 1))
    (a : SimplexCategoryᵒᵖ) (z : (stdSimplex.obj p ⊗ stdSimplex.obj q).obj a)
    (i : Fin (a.unop.len + 1)) :
    (stdSimplex.asOrderHom ((coordinateMap f).app a z).1 i,
      stdSimplex.asOrderHom ((coordinateMap f).app a z).2 i) =
        f (stdSimplex.asOrderHom z.1 i, stdSimplex.asOrderHom z.2 i) := rfl

variable {L m q : SimplexCategory}

/-- For `L, m, q : SimplexCategory` and `τ : L ⟶ m`, the simplicial map
`pullbackMap τ : stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q`
in universe `u` is induced by `(x, k) ↦ (τ.toOrderHom x, k)` on the product ordinals. -/
def pullbackMap (τ : L ⟶ m) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (pullbackCoordinates τ)

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the simplicial map
`domainMap τ ρ : stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q`
in universe `u` is induced by `(x, k) ↦ (τ.toOrderHom x, ρ.toOrderHom x)` on the product ordinals. -/
def domainMap (τ : L ⟶ m) (ρ : L ⟶ q) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (domainCoordinates τ ρ)

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, and `ρ : L ⟶ q`, the simplicial map
`minimumMap τ ρ : stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q`
in universe `u` is induced by `(x, k) ↦ (τ.toOrderHom x, min (ρ.toOrderHom x) k)` on the product ordinals. -/
def minimumMap (τ : L ⟶ m) (ρ : L ⟶ q) :
    stdSimplex.obj L ⊗ stdSimplex.obj q ⟶ stdSimplex.obj m ⊗ stdSimplex.obj q :=
  coordinateMap (minimumCoordinates τ ρ)

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`(pullbackMap τ).app a p = ((stdSimplex.map τ).app a p.1, p.2)`.
The first simplex is mapped by `τ` and the second simplex is retained. -/
theorem pullbackMap_apply (τ : L ⟶ m) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    (pullbackMap τ).app a p = ((stdSimplex.map τ).app a p.1, p.2) := by
  apply Prod.ext
  · rfl
  · exact stdSimplex.ext _ _ (fun _ => rfl)

/-- For `L, m, q : SimplexCategory` and `τ : L ⟶ m`, the morphisms in `SSet.{u}` satisfy
`pullbackMap (q := q) τ = stdSimplex.map τ ▷ stdSimplex.obj q`.
Thus the map induced by `(x, k) ↦ (τ(x), k)` is the product of `stdSimplex.map τ` with the identity of the parameter simplex. -/
theorem pullbackMap_eq_whiskerRight (τ : L ⟶ m) :
    pullbackMap (q := q) τ = SSet.stdSimplex.map τ ▷ SSet.stdSimplex.obj q := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro p
  exact pullbackMap_apply τ a p

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`(domainMap τ ρ).app a p = ((stdSimplex.map τ).app a p.1, (stdSimplex.map ρ).app a p.1)`.
Both output simplices depend on the first input simplex. -/
theorem domainMap_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    (domainMap τ ρ).app a p =
      ((stdSimplex.map τ).app a p.1, (stdSimplex.map ρ).app a p.1) := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, and `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`,
`((minimumMap τ ρ).app a p).1 = (stdSimplex.map τ).app a p.1`.
Taking the minimum in the parameter coordinate leaves this source-map coordinate unchanged. -/
theorem minimumMap_fst_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) :
    ((minimumMap τ ρ).app a p).1 = (stdSimplex.map τ).app a p.1 := rfl

/-- For `L, m, q : SimplexCategory`, `τ : L ⟶ m`, `ρ : L ⟶ q`, `a : SimplexCategoryᵒᵖ`, `p ∈ (stdSimplex.obj L ⊗ stdSimplex.obj q : SSet.{u}).obj a`, and `i : Fin (a.unop.len + 1)`,
`asOrderHom (((minimumMap τ ρ).app a p).2) i = min (ρ.toOrderHom (asOrderHom p.1 i)) (asOrderHom p.2 i)`.
The second output simplex is the pointwise minimum of the source parameter and the independent input parameter. -/
theorem minimumMap_snd_apply (τ : L ⟶ m) (ρ : L ⟶ q) (a : SimplexCategoryᵒᵖ)
    (p : (stdSimplex.obj L ⊗ stdSimplex.obj q).obj a) (i : Fin (a.unop.len + 1)) :
    stdSimplex.asOrderHom (((minimumMap τ ρ).app a p).2) i =
      min (ρ.toOrderHom (stdSimplex.asOrderHom p.1 i)) (stdSimplex.asOrderHom p.2 i) := rfl

/-- Let `F(a) = Fin (a.len + 1)` for `a : SimplexCategory`. Suppose `f : F(L) × F(q) →o F(m) × F(q)` and `f' : F(L') × F(q') →o F(m') × F(q')`, with ordinal maps `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, satisfy
`f.comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp f'`.
Then the induced maps in `SSet.{u}` satisfy
`(stdSimplex.map δ ⊗ₘ stdSimplex.map α) ≫ coordinateMap f = coordinateMap f' ≫ (stdSimplex.map γ ⊗ₘ stdSimplex.map α)`. -/
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
