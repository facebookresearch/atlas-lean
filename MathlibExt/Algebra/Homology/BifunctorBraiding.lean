/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

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

@[simp]
theorem mapBifunctorBraidingIso_hom_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorBraidingIso K L).hom.f p).f q =
      (β_ (K.X p) (L.X q)).hom :=
  rfl

@[simp]
theorem mapBifunctorBraidingIso_inv_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorBraidingIso K L).inv.f p).f q =
      (β_ (K.X p) (L.X q)).inv :=
  rfl

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

@[simp]
theorem mapBifunctorFlipBraidingIso_hom_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorFlipBraidingIso K L).hom.f p).f q =
      (β_ (L.X q) (K.X p)).hom :=
  rfl

@[simp]
theorem mapBifunctorFlipBraidingIso_inv_f_f
    (K : HomologicalComplex C c₁) (L : HomologicalComplex C c₂)
    (p : I₁) (q : I₂) :
    ((mapBifunctorFlipBraidingIso K L).inv.f p).f q =
      (β_ (L.X q) (K.X p)).inv :=
  rfl

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
