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

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    i₂ A B ≫ c₁₂ A B = i₁ A B ≫ c₂₃ A B :=
  i₂_c₁₂ A B

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    i₂ A B ≫ c₁₃ A B = i₂ A B ≫ c₂₃ A B :=
  i₂_c₁₃ A B

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    (i₂ A B).hom b = 1 ⊗ₜ b :=
  i₂_apply A B b

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b b' : B) :
    (c₂₃ A B).hom (b ⊗ₜ b') = 1 ⊗ₜ (b ⊗ₜ b') :=
  c₂₃_tmul A B b b'

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b b' : B) :
    (c₁₃ A B).hom (b ⊗ₜ b') = b ⊗ₜ (1 ⊗ₜ b') :=
  c₁₃_tmul A B b b'

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    CommRingCat.ofHom (algebraMap A B) ≫ i₁ A B =
      CommRingCat.ofHom (algebraMap A B) ≫ i₂ A B :=
  algebraMap_i₁_eq_i₂ A B

example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    (i₁ A B).hom.comp (algebraMap A B) = (i₂ A B).hom.comp (algebraMap A B) :=
  i₁_comp_algebraMap_eq A B

/-- The canonical comparison is an isomorphism between the two pullbacks. -/
example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{0} A) :
    (ModuleCat.extendScalars (i₁ A B).hom).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  canonical A B M

/-- The canonical descent isomorphism satisfies the cocycle condition. -/
example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{0} A) :
    Cocycle ((ModuleCat.extendScalars (algebraMap A B)).obj M) (canonical A B M) :=
  canonical_cocycle M
