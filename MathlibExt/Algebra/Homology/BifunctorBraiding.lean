/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding the tensor bifunctor on two complex directions

Let C be preadditive and braided monoidal, with tensor product additive in each variable. For
complexes K and L of arbitrary shapes c₁ and c₂, the braiding β_(K_p,L_q) defines an
isomorphism between their tensor-bifunctor bicomplex and the bicomplex of the flipped tensor
bifunctor. Both keep the first complex direction indexed by p and the second by q; only the
order of the tensor factors changes.

The oppositely oriented construction uses β_(L_q,K_p), and both constructions are natural in K
and L. The inverse component formulas use β_(K_p,L_q).inv and β_(L_q,K_p).inv, respectively.
These are cellwise comparisons with unchanged complex axes, so no total-complex sign enters
them.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ T : C, ((curriedTensor C).obj T).Additive]
  [BraidedCategory C]
variable {I₁ : Type w₁} {I₂ : Type w₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. mapBifunctorBraidingIso compares the bicomplex with cells K_p ⊗
L_q to the one with cells L_q ⊗ K_p, both of shape (c₁,c₂). Its cell (p,q) forward map is
β_(K_p,L_q).hom and inverse map is β_(K_p,L_q).inv; braiding naturality gives both
differential squares. -/
noncomputable def mapBifunctorBraidingIso
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    (((curriedTensor C).mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L ≅
      (((curriedTensor C).flip.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => β_ (K.X p) (L.X q))
      (fun i j _ => by
        change (β_ (K.X p) (L.X i)).hom ≫ L.d i j ▷ K.X p =
          K.X p ◁ L.d i j ≫ (β_ (K.X p) (L.X j)).hom
        rw [← BraidedCategory.braiding_naturality_right]))
    (fun i j _ => by
      ext q
      change (β_ (K.X i) (L.X q)).hom ≫ L.X q ◁ K.d i j =
        K.d i j ▷ L.X q ≫ (β_ (K.X j) (L.X q)).hom
      rw [BraidedCategory.braiding_naturality_left])

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. For p and q in the two index types, ((mapBifunctorBraidingIso K
L).hom.f p).f q = β_(K.X p,L.X q).hom. -/
@[simp]
theorem mapBifunctorBraidingIso_hom_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorBraidingIso K L).hom.f p).f q =
      (β_ (K.X p) (L.X q)).hom :=
  rfl

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. For p and q, ((mapBifunctorBraidingIso K L).inv.f p).f q =
β_(K.X p,L.X q).inv. -/
@[simp]
theorem mapBifunctorBraidingIso_inv_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorBraidingIso K L).inv.f p).f q =
      (β_ (K.X p) (L.X q)).inv :=
  rfl

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. mapBifunctorFlipBraidingIso maps cells L_q ⊗ K_p to K_p ⊗ L_q
by β_(L_q,K_p).hom, with inverse β_(L_q,K_p).inv. The shapes and complex-direction order
remain (c₁,c₂). This uses the reverse oriented braiding, rather than identifying it with
β_(K_p,L_q).inv. -/
noncomputable def mapBifunctorFlipBraidingIso
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    (((curriedTensor C).flip.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L ≅
      (((curriedTensor C).mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => β_ (L.X q) (K.X p))
      (fun i j _ => by
        change (β_ (L.X i) (K.X p)).hom ≫ K.X p ◁ L.d i j =
          L.d i j ▷ K.X p ≫ (β_ (L.X j) (K.X p)).hom
        rw [BraidedCategory.braiding_naturality_left]))
    (fun i j _ => by
      ext q
      change (β_ (L.X q) (K.X i)).hom ≫ K.d i j ▷ L.X q =
        L.X q ◁ K.d i j ≫ (β_ (L.X q) (K.X j)).hom
      rw [← BraidedCategory.braiding_naturality_right])

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. For p and q, ((mapBifunctorFlipBraidingIso K L).hom.f p).f q =
β_(L.X q,K.X p).hom. -/
@[simp]
theorem mapBifunctorFlipBraidingIso_hom_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorFlipBraidingIso K L).hom.f p).f q =
      (β_ (L.X q) (K.X p)).hom :=
  rfl

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. For p and q, ((mapBifunctorFlipBraidingIso K L).inv.f p).f q =
β_(L.X q,K.X p).inv. -/
@[simp]
theorem mapBifunctorFlipBraidingIso_inv_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorFlipBraidingIso K L).inv.f p).f q =
      (β_ (L.X q) (K.X p)).inv :=
  rfl

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. For arbitrary shapes c₁,c₂, mapBifunctorBraidingNatIso is a natural
isomorphism from curriedTensor C mapped to c₁- and c₂-complexes to its flipped-bifunctor
counterpart. Its component at K,L is mapBifunctorBraidingIso K L, with cell map
β_(K_p,L_q).hom. -/
noncomputable def mapBifunctorBraidingNatIso :
    (curriedTensor C).mapBifunctorHomologicalComplex c₁ c₂ ≅
      (curriedTensor C).flip.mapBifunctorHomologicalComplex c₁ c₂ :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun L => mapBifunctorBraidingIso K L) (fun f => by
      ext p q
      exact BraidedCategory.braiding_naturality_right (K.X p) (f.f q)))
    (fun f => by
      ext L p q
      exact BraidedCategory.braiding_naturality_left (f.f p) (L.X q))

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. For arbitrary shapes c₁,c₂, mapBifunctorFlipBraidingNatIso is the natural
isomorphism from the flipped tensor-bifunctor complex construction to the tensor-bifunctor
construction. Its component at K,L is mapBifunctorFlipBraidingIso K L, using β_(L_q,K_p).hom. -/
noncomputable def mapBifunctorFlipBraidingNatIso :
    (curriedTensor C).flip.mapBifunctorHomologicalComplex c₁ c₂ ≅
      (curriedTensor C).mapBifunctorHomologicalComplex c₁ c₂ :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun L => mapBifunctorFlipBraidingIso K L) (fun f => by
      ext p q
      exact BraidedCategory.braiding_naturality_left (f.f q) (K.X p)))
    (fun f => by
      ext L p q
      exact BraidedCategory.braiding_naturality_right (L.X q) (f.f p))

@[simp]
theorem mapBifunctorBraidingNatIso_hom_app_app
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    ((mapBifunctorBraidingNatIso.hom.app K).app L) =
      (mapBifunctorBraidingIso K L).hom := rfl

@[simp]
theorem mapBifunctorBraidingNatIso_inv_app_app
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    ((mapBifunctorBraidingNatIso.inv.app K).app L) =
      (mapBifunctorBraidingIso K L).inv := rfl

@[simp]
theorem mapBifunctorFlipBraidingNatIso_hom_app_app
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    ((mapBifunctorFlipBraidingNatIso.hom.app K).app L) =
      (mapBifunctorFlipBraidingIso K L).hom := rfl

@[simp]
theorem mapBifunctorFlipBraidingNatIso_inv_app_app
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂) :
    ((mapBifunctorFlipBraidingNatIso.inv.app K).app L) =
      (mapBifunctorFlipBraidingIso K L).inv := rfl

end HomologicalComplex
