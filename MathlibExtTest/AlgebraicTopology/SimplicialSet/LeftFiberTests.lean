/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.LeftFiber

/-!
# Simplicial left-fiber tests

Focused checks for the pullback definition, its two projections, the
arbitrary-degree simplex description, and contravariant reindexing of the
simplex-category coordinate.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.LeftFiberTests

variable {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ} (y : Y _⦋m⦌)

/-- The left fiber is the advertised pullback. -/
example : SSet.leftFiber (X := X) (Y := Y) f (m := m) y =
    pullback f (SSet.yonedaEquiv.symm y) :=
  rfl

/-- The projections form the defining commutative square. -/
example :
    SSet.leftFiber.π (X := X) (Y := Y) f (m := m) y ≫ f =
      SSet.leftFiber.toSimplex (X := X) (Y := Y) f (m := m) y ≫
        SSet.yonedaEquiv.symm y :=
  SSet.leftFiber.condition (X := X) (Y := Y) f (m := m) y

/-- Simplices have the expected pair-and-compatibility description. -/
noncomputable example (a : SimplexCategoryᵒᵖ) :
    (SSet.leftFiber (X := X) (Y := Y) f (m := m) y).obj a ≃
      {_p : X.obj a × (a.unop ⟶ ⦋m⦌) //
        f.app a _p.1 = Y.map _p.2.op y} :=
  SSet.leftFiber.objEquiv (X := X) (Y := Y) f (m := m) y a

-- The public computation interface exposes both pullback projections and the
-- full two-coordinate reindex law.
#check @SSet.leftFiber.objEquiv_fst
#check @SSet.leftFiber.objEquiv_snd
#check @SSet.leftFiber.objEquiv_map

end MathlibExtTest.AlgebraicTopology.SimplicialSet.LeftFiberTests

end
