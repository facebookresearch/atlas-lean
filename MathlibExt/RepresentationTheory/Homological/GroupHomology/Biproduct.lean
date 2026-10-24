/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Group homology preserves binary biproducts

For `G`-modules `A` and `B`, group homology splits over a direct sum:
`Hₙ(G, A ⊕ B) ≅ Hₙ(G, A) ⊕ Hₙ(G, B)`, and the isomorphism commutes with
the inclusion and projection maps. This is Corollary 23.22 of ATLAS
`NumberTheoryI`, Section 23.2.

The new content is the additivity of the chains functor: Mathlib has the
corresponding instance for the cochains functor
(`groupCohomology.cochainsFunctor`), but only `PreservesZeroMorphisms`
for the chains functor. Once additivity is registered, the isomorphism
is `Functor.mapBiprod` for the homology functor.
-/

@[expose] public section

open CategoryTheory Limits

namespace groupHomology

universe u

/-- Additivity of `Finsupp.mapRange.linearMap` in the linear map. -/
private lemma mapRange_linearMap_add_apply {k : Type u}
    [CommRing k] {α M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (f g : M →ₗ[k] N) (x : α →₀ M) :
    Finsupp.mapRange.linearMap (f + g) x =
      Finsupp.mapRange.linearMap f x + Finsupp.mapRange.linearMap g x := by
  ext i
  simp [Finsupp.mapRange.linearMap_apply]

/-- The inhomogeneous-chains functor of group homology is additive. -/
instance chainsFunctor_additive (k G : Type u) [CommRing k] [Group G] :
    (chainsFunctor k G).Additive where
  map_add {X Y f g} := by
    ext n : 1
    change (chainsMap (MonoidHom.id G) (f + g)).f n =
      ((chainsMap (MonoidHom.id G) f) + (chainsMap (MonoidHom.id G) g)).f n
    have key : ∀ (φ : X ⟶ Y), (chainsMap (MonoidHom.id G) φ).f n =
        ModuleCat.ofHom
          (Finsupp.mapRange.linearMap (Rep.Hom.hom φ).toLinearMap ∘ₗ
            Finsupp.lmapDomain (↑X) k fun x => (MonoidHom.id G) ∘ x) :=
      fun φ => chainsMap_f (MonoidHom.id G) φ n
    rw [key (f + g)]
    conv_rhs =>
      rw [show (chainsMap (MonoidHom.id G) f +
          chainsMap (MonoidHom.id G) g).f n =
          (chainsMap (MonoidHom.id G) f).f n +
          (chainsMap (MonoidHom.id G) g).f n from rfl, key f, key g]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((Finsupp.mapRange.linearMap (Rep.Hom.hom (f + g)).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) =
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom f).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) +
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom g).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x)
    simp only [LinearMap.comp_apply]
    rw [show (Rep.Hom.hom (f + g)).toLinearMap =
      (Rep.Hom.hom f).toLinearMap + (Rep.Hom.hom g).toLinearMap from rfl]
    exact mapRange_linearMap_add_apply _ _ _

/-- The `n`th group-homology functor is additive. -/
instance functor_additive (k G : Type u) [CommRing k] [Group G] (n : ℕ) :
    (functor k G n).Additive :=
  Functor.additive_of_iso
    (Iso.refl (chainsFunctor k G ⋙
        HomologicalComplex.homologyFunctor (ModuleCat k)
          (ComplexShape.down ℕ) n) :
      chainsFunctor k G ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k)
            (ComplexShape.down ℕ) n ≅
        functor k G n)

/-- The `n`th group-homology functor preserves binary biproducts. -/
instance functor_preservesBinaryBiproducts (k G : Type u)
    [CommRing k] [Group G] (n : ℕ) :
    PreservesBinaryBiproducts (functor k G n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Group homology of a direct sum is the direct sum of the group
homologies (Corollary 23.22). -/
noncomputable def biprodIso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupHomology (A ⊞ B) n ≅ groupHomology A n ⊞ groupHomology B n :=
  (functor k G n).mapBiprod A B

/-- The forward map of `biprodIso` is the lift of the maps induced by
the two projections. -/
theorem biprodIso_hom (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom =
      biprod.lift (groupHomology.map (MonoidHom.id G) biprod.fst n)
        (groupHomology.map (MonoidHom.id G) biprod.snd n) := rfl

/-- The backward map of `biprodIso` is the descent of the maps induced
by the two inclusions. -/
theorem biprodIso_inv (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).inv =
      biprod.desc (groupHomology.map (MonoidHom.id G) biprod.inl n)
        (groupHomology.map (MonoidHom.id G) biprod.inr n) := rfl

/-- `biprodIso` commutes with the first projection. -/
theorem biprodIso_hom_fst (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom ≫ biprod.fst =
      groupHomology.map (MonoidHom.id G) biprod.fst n := by
  rw [biprodIso_hom]
  exact biprod.lift_fst _ _

/-- `biprodIso` commutes with the second projection. -/
theorem biprodIso_hom_snd (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom ≫ biprod.snd =
      groupHomology.map (MonoidHom.id G) biprod.snd n := by
  rw [biprodIso_hom]
  exact biprod.lift_snd _ _

/-- `biprodIso` commutes with the first inclusion. -/
theorem biprodIso_inv_inl (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    biprod.inl ≫ (biprodIso k G A B n).inv =
      groupHomology.map (MonoidHom.id G) biprod.inl n := by
  rw [biprodIso_inv, biprod.inl_desc]

/-- `biprodIso` commutes with the second inclusion. -/
theorem biprodIso_inv_inr (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    biprod.inr ≫ (biprodIso k G A B n).inv =
      groupHomology.map (MonoidHom.id G) biprod.inr n := by
  rw [biprodIso_inv, biprod.inr_desc]

end groupHomology
