/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Functoriality of `TopCat` zeroth homotopy

Lightweight shared module holding the generic `TopCat` zeroth-homotopy API:
the map on `ZerothHomotopy` induced by a continuous map, its `mk`/`id`/`comp`
laws, the functor to `Type`, and both `zerothHomotopyEquiv` naturality
directions. The block is moved verbatim in public names, types, and semantics
from `MathlibExt.AlgebraicTopology.SingularHomology.HomologyZero` so that the
singular-homology and simplicial `π₀` consumers can share one low module below
the homology layer; their migrations follow in subsequent one-file steps and
are neither edited nor imported here.

Nonclaims: no homology theorem, no additivity, no `π₀`-identification beyond the
two stated naturalities, and no coproduct functor (that stays with homology).
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
