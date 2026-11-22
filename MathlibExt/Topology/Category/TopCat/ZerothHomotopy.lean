/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Functoriality of zeroth homotopy in `TopCat`

A continuous map induces a map on `ZerothHomotopy`, with computation on
representatives and identity and composition laws. These maps form the
functor `zerothHomotopyFunctor : TopCat ⥤ Type`. The equivalence
`zerothHomotopyEquiv` is natural in both its forward and inverse directions.
-/

@[expose] public section

universe w

open CategoryTheory

/- Functoriality of `ZerothHomotopy` and compatibility with `SSet.π₀`. -/
namespace TopCat

variable {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The map on zeroth homotopy induced by a continuous map, defined by quotient lift. -/
noncomputable def zerothHomotopyMap (f : X ⟶ Y) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.hom.continuous))

/-- Representative law: the induced map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem zerothHomotopyMap_mk (f : X ⟶ Y) (x : X) :
    zerothHomotopyMap f (.mk x) = .mk (f x) :=
  rfl

/-- Identity law: the map induced by `𝟙 X` is the identity. -/
@[simp]
theorem zerothHomotopyMap_id_apply (x : ZerothHomotopy X) :
    zerothHomotopyMap (𝟙 X) x = x := by
  induction x using ZerothHomotopy.rec
  simp

/-- Composition law: the map induced by `f ≫ g` is the composite of the induced maps. -/
@[simp]
theorem zerothHomotopyMap_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : ZerothHomotopy X) :
    zerothHomotopyMap (f ≫ g) x = zerothHomotopyMap g (zerothHomotopyMap f x) := by
  induction x using ZerothHomotopy.rec
  simp

/-- The functor `TopCat ⥤ Type` sending `X` to `ZerothHomotopy X`. -/
noncomputable def zerothHomotopyFunctor : TopCat.{w} ⥤ Type w where
  obj X := ZerothHomotopy X
  map f := ↾(zerothHomotopyMap f)

/-- Object law: the functor sends `X` to `ZerothHomotopy X`. -/
@[simp]
theorem zerothHomotopyFunctor_obj (X : TopCat.{w}) :
    (zerothHomotopyFunctor.{w}).obj X = ZerothHomotopy X :=
  rfl

/-- Map law: the functor sends `f` to the function induced by `zerothHomotopyMap f`. -/
@[simp]
theorem zerothHomotopyFunctor_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (zerothHomotopyFunctor.{w}).map f = ↾(zerothHomotopyMap f) :=
  rfl

/-- Naturality of `zerothHomotopyEquiv` against `zerothHomotopyMap` and `SSet.mapπ₀`. -/
@[simp]
theorem zerothHomotopyEquiv_naturality (f : X ⟶ Y) (x : ZerothHomotopy X) :
    zerothHomotopyEquiv (zerothHomotopyMap f x) =
      SSet.mapπ₀ (TopCat.toSSet.map f) (zerothHomotopyEquiv x) := by
  induction x using ZerothHomotopy.rec
  rfl

/-- Naturality of the inverse `zerothHomotopyEquiv`. -/
theorem zerothHomotopyEquiv_symm_naturality (f : X ⟶ Y)
    (y : (TopCat.toSSet.obj X).π₀) :
    zerothHomotopyEquiv.symm (SSet.mapπ₀ (TopCat.toSSet.map f) y) =
      zerothHomotopyMap f (zerothHomotopyEquiv.symm y) := by
  induction y using SSet.π₀.rec
  rfl

end TopCat
