/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricallyConnected

@[expose] public section

open AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f :=
  AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected f
