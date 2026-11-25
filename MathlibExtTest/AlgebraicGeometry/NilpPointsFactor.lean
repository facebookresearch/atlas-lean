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

universe u

/-- `Scheme.pointsOver` acts on morphisms by precomposition with their `Spec`, in any universe. -/
example {𝒪 : Type u} [CommRing 𝒪] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of 𝒪))
    {B B' : CommAlgCat.{u} 𝒪} (g : B ⟶ B') (φ : (Scheme.pointsOver f).obj B) :
    ((Scheme.pointsOver f).map g φ).1 = Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ φ.1 := by
  simp

/-- `Scheme.pointsOver` is a functor, so the standard functor lemmas apply to it. -/
example {𝒪 : Type u} [CommRing 𝒪] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (B : CommAlgCat.{u} 𝒪) : (Scheme.pointsOver f).map (𝟙 B) = 𝟙 _ :=
  (Scheme.pointsOver f).map_id B

/-- `Scheme.pointsOver.mapHom` composes points with the morphism of schemes. -/
example {𝒪 : Type u} [CommRing 𝒪] {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of 𝒪))
    (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (h : X ⟶ Y) (w : h ≫ fY = fX) {B : CommAlgCat.{u} 𝒪}
    (φ : (Scheme.pointsOver fX).obj B) :
    ((Scheme.pointsOver.mapHom fX fY h w).app B φ).1 = φ.1 ≫ h := by
  simp

/-- Consumer with the binders of the theorem. -/
example {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).asIso.hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p)
    (hsec : Function.Injective p.appTop.hom)
    (hinv : Set.range p.appTop.hom =
      {s | ∀ g : G, (ρ g).asIso.hom.appTop.hom s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ B : CommAlgCat.{0} 𝒪,
      IsNilpotent (algebraMap 𝒪 B π) → (Scheme.pointsOver fM).obj B →
        (Scheme.pointsOver t).obj B)
    (hu_nat : ∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B')
      (x : (Scheme.pointsOver fM).obj B),
      u B' hB' ((Scheme.pointsOver fM).map φ x) =
        (Scheme.pointsOver t).map φ (u B hB x))
    (hu_inv : ∀ (B : CommAlgCat.{0} 𝒪)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G)
      (y : (Scheme.pointsOver fM).obj B),
      u B hB ((Scheme.pointsOver.mapHom fM fM (ρ g).asIso.hom (hover g)).app B y) =
        u B hB y)
    (hX : IsAffine X) (hT : IsAffine T) :
    ∃ ubar : ∀ B : CommAlgCat.{0} 𝒪,
        IsNilpotent (algebraMap 𝒪 B π) → (Scheme.pointsOver f).obj B →
          (Scheme.pointsOver t).obj B,
      (∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B')
          (x : (Scheme.pointsOver f).obj B),
          ubar B' hB' ((Scheme.pointsOver f).map φ x) =
            (Scheme.pointsOver t).map φ (ubar B hB x)) ∧
        (∀ (B : CommAlgCat.{0} 𝒪)
          (hB : IsNilpotent (algebraMap 𝒪 B π))
          (y : (Scheme.pointsOver fM).obj B),
          ubar B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) =
            u B hB y) ∧
        ∀ u' : ∀ B : CommAlgCat.{0} 𝒪,
            IsNilpotent (algebraMap 𝒪 B π) → (Scheme.pointsOver f).obj B →
              (Scheme.pointsOver t).obj B,
          (∀ (B B' : CommAlgCat.{0} 𝒪)
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B')
              (x : (Scheme.pointsOver f).obj B),
              u' B' hB' ((Scheme.pointsOver f).map φ x) =
                (Scheme.pointsOver t).map φ (u' B hB x)) →
            (∀ (B : CommAlgCat.{0} 𝒪)
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (y : (Scheme.pointsOver fM).obj B),
              u' B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) =
                u B hB y) →
            ∀ (B : CommAlgCat.{0} 𝒪)
              (hB : IsNilpotent (algebraMap 𝒪 B π))
              (z : (Scheme.pointsOver f).obj B), u' B hB z = ubar B hB z :=
  AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
    π fM f hlft hlftX ρ hover p hp hρp hint haff hsec hinv T t u hu_nat
    hu_inv hX hT
