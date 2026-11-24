/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NilpPointsFactor

@[expose] public section

open CategoryTheory AlgebraicGeometry

/-- Consumer with the original binders. -/
example {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).asIso.hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p)
    (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).asIso.hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B],
      IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B →
        (Scheme.nilpPoints t).obj B)
    (hu_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type)
      [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (x : (Scheme.nilpPoints fM).obj B),
      u B' hB' ((Scheme.nilpPoints fM).map φ x) =
        (Scheme.nilpPoints t).map φ (u B hB x))
    (hu_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G)
      (y : (Scheme.nilpPoints fM).obj B),
      u B hB ((Scheme.nilpPoints.mapHom fM fM (ρ g).asIso.hom (hover g)).app B y) =
        u B hB y)
    (hX : IsAffine X) (hT : IsAffine T) :
    ∃ ubar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B],
        IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B →
          (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B']
          [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
          (x : (Scheme.nilpPoints f).obj B),
          ubar B' hB' ((Scheme.nilpPoints f).map φ x) =
            (Scheme.nilpPoints t).map φ (ubar B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
          (hB : IsNilpotent (algebraMap 𝒪 B π))
          (y : (Scheme.nilpPoints fM).obj B),
          ubar B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) =
            u B hB y) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B],
            IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B →
              (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type)
              [CommRing B'] [Algebra 𝒪 B']
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
              (x : (Scheme.nilpPoints f).obj B),
              u' B' hB' ((Scheme.nilpPoints f).map φ x) =
                (Scheme.nilpPoints t).map φ (u' B hB x)) →
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (y : (Scheme.nilpPoints fM).obj B),
              u' B hB ((Scheme.nilpPoints.mapHom fM f p hp).app B y) =
                u B hB y) →
            ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (z : (Scheme.nilpPoints f).obj B), u' B hB z = ubar B hB z :=
  AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
    π fM f hlft hlftX ρ hover p hp hρp hint haff hsurj hsec hinv T t u hu_nat
    hu_inv hX hT
