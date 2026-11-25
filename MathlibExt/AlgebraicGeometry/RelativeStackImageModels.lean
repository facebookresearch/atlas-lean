/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackFibreModels

/-!
# The same native fibred category viewed over a new base

For f:Y to X, the source total category is the original Grothendieck
category of R_Y, with base map composed through Over.map f. This retains
the actual lift T to Y and the root family over that lift, including
all arrows. A native stack realization compares its entire total category
to that exact source category and fixes its complete base functor.

Source: Talpo--Vistoli1410.1164v2, Section6 and Proposition6.14.
The corresponding root map and its fppf property are separate operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeStackImageModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (R : Stack Y)

/-- Exact original family base, now composed with the specified scheme map. -/
def baseFunctor : Total R ⥤ Over X :=
  Pseudofunctor.CoGrothendieck.forget R.toPseudofunctor ⋙ Over.map f

/-- The whole source category, not just field-valued fibres or object counts. -/
structure ImageModel where
  stack : Stack X
  comparison : Total stack ≌ Total R
  base_eq : comparison.functor ⋙ baseFunctor f R =
    Pseudofunctor.CoGrothendieck.forget stack.toPseudofunctor

end MathlibExt.AlgebraicGeometry.RelativeStackImageModels
