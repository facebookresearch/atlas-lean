/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothRelDim

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f :=
  AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace f
