/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.DescentCofaces

@[expose] public section

open TensorProduct CategoryTheory Algebra.DescentCofaces

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    (i₁ A B).hom b = b ⊗ₜ 1 :=
  i₁_apply A B b

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b b' : B) :
    (c₁₂ A B).hom (b ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ 1) :=
  c₁₂_tmul A B b b'

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    i₁ A B ≫ c₁₂ A B = i₁ A B ≫ c₁₃ A B :=
  i₁_c₁₂ A B
