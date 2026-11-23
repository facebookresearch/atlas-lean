/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ClosedImmersionIsIso

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i :=
  AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i g f w h
