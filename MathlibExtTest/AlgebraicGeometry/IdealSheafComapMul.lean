/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IdealSheafComapMul

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

-- Consumer with the original binders.
example {X Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f :=
  AlgebraicGeometry.Scheme.IdealSheafData.comap_mul I J f

universe v

-- The same consumer for schemes in a higher universe.
example {X Y : Scheme.{v}} (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f :=
  AlgebraicGeometry.Scheme.IdealSheafData.comap_mul I J f

-- Boundary: pullback along the identity is the identity, so the formula
-- specialises to the tautology `I * J = I * J`; multiplication is not
-- collapsed, as `⊤ * ⊥ = ⊥ ≠ ⊤` on ideal sheaf data with a nontrivial
-- bottom distinct from the top would already fail at the level of ideals.
example {Y : Scheme.{u}} (I J : Y.IdealSheafData) :
    (I * J).comap (𝟙 Y) = I * J := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_mul,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
