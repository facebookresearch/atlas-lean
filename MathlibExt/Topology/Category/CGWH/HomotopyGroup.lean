/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic
public import MathlibExt.Topology.Category.TopCat.ZerothHomotopy

/-!
# Zeroth homotopy of compactly generated weak Hausdorff spaces

The native CGWH inclusion into topological spaces transports the existing
zeroth-homotopy functor without adding any model-category structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory

namespace CGWH

/-- The set of path components of a CGWH space. -/
noncomputable def piZero (X : CGWH.{u, v}) : Type v :=
  ZerothHomotopy (CGWH.cgwhToTop.obj X)

/-- Zeroth homotopy as a functor from CGWH spaces to types. -/
noncomputable def piZeroFunctor : CGWH.{u, v} ⥤ Type v :=
  CGWH.cgwhToTop.{u, v} ⋙ TopCat.zerothHomotopyFunctor

/-- The map on path components induced by a CGWH map. -/
noncomputable def piZeroMap {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    piZero X → piZero Y :=
  (piZeroFunctor.{u, v}).map f

/-- The induced map on path components sends a representative to its image. -/
@[simp]
theorem piZeroMap_mk {X Y : CGWH.{u, v}} (f : X ⟶ Y) (x : X) :
    piZeroMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) :=
  rfl

end CGWH
