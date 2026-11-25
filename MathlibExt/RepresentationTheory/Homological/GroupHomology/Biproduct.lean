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
`NumberTheoryI`, Section 23.4.

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

/-- **Group homology of a direct sum.** Let $k$ be a commutative ring, $G$ a group, $A$ and $B$
representations of $G$ over $k$, and $n \in \mathbb{N}$, and write $H_n(G, M)$ for the $n$th group
homology of a representation $M$. This is the isomorphism
$H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ obtained by applying the $n$th group homology
functor, which is additive, to the biproduct $A \oplus B$.

Source: NumberTheoryI, Section 23.4, Corollary 23.22. -/
noncomputable def biprodIso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupHomology (A ⊞ B) n ≅ groupHomology A n ⊞ groupHomology B n :=
  (functor k G n).mapBiprod A B

/-- **Forward map of the direct-sum isomorphism in group homology.** Let $k$ be a commutative
ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$, and write
$H_n(G, M)$ for the $n$th group homology of a representation $M$. The forward map of the
isomorphism $H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ is the map into the biproduct
whose components are the maps $H_n(G, A \oplus B) \to H_n(G, A)$ and
$H_n(G, A \oplus B) \to H_n(G, B)$ induced by the projections $A \oplus B \to A$ and
$A \oplus B \to B$. -/
theorem biprodIso_hom (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom =
      biprod.lift (groupHomology.map (MonoidHom.id G) biprod.fst n)
        (groupHomology.map (MonoidHom.id G) biprod.snd n) := rfl

/-- **Inverse map of the direct-sum isomorphism in group homology.** Let $k$ be a commutative
ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$, and write
$H_n(G, M)$ for the $n$th group homology of a representation $M$. The inverse map of the
isomorphism $H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ is the map out of the biproduct
whose components are the maps $H_n(G, A) \to H_n(G, A \oplus B)$ and
$H_n(G, B) \to H_n(G, A \oplus B)$ induced by the inclusions $A \to A \oplus B$ and
$B \to A \oplus B$. -/
theorem biprodIso_inv (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).inv =
      biprod.desc (groupHomology.map (MonoidHom.id G) biprod.inl n)
        (groupHomology.map (MonoidHom.id G) biprod.inr n) := rfl

/-- **Direct-sum isomorphism in group homology and the first projection.** Let $k$ be a
commutative ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$,
and write $H_n(G, M)$ for the $n$th group homology of a representation $M$. The isomorphism
$H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ followed by the projection onto $H_n(G, A)$
equals the map $H_n(G, A \oplus B) \to H_n(G, A)$ induced by the projection $A \oplus B \to A$. -/
theorem biprodIso_hom_fst (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom ≫ biprod.fst =
      groupHomology.map (MonoidHom.id G) biprod.fst n := by
  rw [biprodIso_hom]
  exact biprod.lift_fst _ _

/-- **Direct-sum isomorphism in group homology and the second projection.** Let $k$ be a
commutative ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$,
and write $H_n(G, M)$ for the $n$th group homology of a representation $M$. The isomorphism
$H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ followed by the projection onto $H_n(G, B)$
equals the map $H_n(G, A \oplus B) \to H_n(G, B)$ induced by the projection $A \oplus B \to B$. -/
theorem biprodIso_hom_snd (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    (biprodIso k G A B n).hom ≫ biprod.snd =
      groupHomology.map (MonoidHom.id G) biprod.snd n := by
  rw [biprodIso_hom]
  exact biprod.lift_snd _ _

/-- **Direct-sum isomorphism in group homology and the first inclusion.** Let $k$ be a
commutative ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$,
and write $H_n(G, M)$ for the $n$th group homology of a representation $M$. The inclusion of
$H_n(G, A)$ into $H_n(G, A) \oplus H_n(G, B)$ followed by the inverse of the isomorphism
$H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ equals the map
$H_n(G, A) \to H_n(G, A \oplus B)$ induced by the inclusion $A \to A \oplus B$. -/
theorem biprodIso_inv_inl (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    biprod.inl ≫ (biprodIso k G A B n).inv =
      groupHomology.map (MonoidHom.id G) biprod.inl n := by
  rw [biprodIso_inv, biprod.inl_desc]

/-- **Direct-sum isomorphism in group homology and the second inclusion.** Let $k$ be a
commutative ring, $G$ a group, $A$ and $B$ representations of $G$ over $k$, and $n \in \mathbb{N}$,
and write $H_n(G, M)$ for the $n$th group homology of a representation $M$. The inclusion of
$H_n(G, B)$ into $H_n(G, A) \oplus H_n(G, B)$ followed by the inverse of the isomorphism
$H_n(G, A \oplus B) \cong H_n(G, A) \oplus H_n(G, B)$ equals the map
$H_n(G, B) \to H_n(G, A \oplus B)$ induced by the inclusion $B \to A \oplus B$. -/
theorem biprodIso_inv_inr (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    biprod.inr ≫ (biprodIso k G A B n).inv =
      groupHomology.map (MonoidHom.id G) biprod.inr n := by
  rw [biprodIso_inv, biprod.inr_desc]

end groupHomology
