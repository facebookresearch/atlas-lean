/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.CorepresentableFaithfullyFlat

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

theorem exactSource_corepresentable
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B,
            F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] (hflat : (algebraMap R S₁).Flat)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S₁)))
    (C₁ : Under (CommRingCat.of R)) (c : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ C₁)
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶
        B'),
      F.obj B' ≃ {g : C₁ ⟶ B' // c ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁))
        ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'),
      ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) :=
  CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ F hsheaf S₁ hflat
      hsurj C₁ c e he
