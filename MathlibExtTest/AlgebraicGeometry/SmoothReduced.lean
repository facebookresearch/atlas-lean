/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothReduced

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

example {k : Type u} [Field k] {Z : Scheme.{u}} {g : Z ⟶ Spec (.of k)} (hg : Smooth g) :
    IsReduced Z :=
  AlgebraicGeometry.isReduced_of_smooth_over_field hg
