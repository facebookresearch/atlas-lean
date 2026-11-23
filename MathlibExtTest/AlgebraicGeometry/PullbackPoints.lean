/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PullbackPoints

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

example {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : ↥(pullback f g)}
    (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
    (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂)
    [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))] :
    t₁ = t₂ :=
  AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap h₁ h₂
