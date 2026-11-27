/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LineBundlePullback

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open CategoryTheory _root_.AlgebraicGeometry

universe u

-- Pullbacks of invertible sheaves are invertible, for instance of the structure sheaf.
example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsLineBundle ((Scheme.Modules.pullback f).obj (structureModule Y)) :=
  (isLineBundle_structureModule Y).pullback f

-- Pulling back twice.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {L : Z.Modules} (hL : IsLineBundle L) :
    IsLineBundle ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L)) :=
  (hL.pullback g).pullback f

-- The structure sheaf pulls back to the structure sheaf.
noncomputable example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X :=
  pullbackStructureModuleIso f

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
