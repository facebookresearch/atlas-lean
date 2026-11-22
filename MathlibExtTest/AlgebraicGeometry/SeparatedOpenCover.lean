/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SeparatedOpenCover

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem exactSource {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g :=
  AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover g 𝒰 h
