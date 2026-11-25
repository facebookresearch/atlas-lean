/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import MathlibExt.CategoryTheory.Products.Limits

/-!
# Additive structure on product categories

For preadditive categories `C` and `D`, the product `C × D` carries a
componentwise preadditive structure: hom groups are products of hom groups and
composition is componentwise. The projections `Prod.fst` and `Prod.snd` are
additive. The product zero object is provided by
`MathlibExt.CategoryTheory.Products.Limits`. With binary biproducts in each
factor, the product has
binary biproducts componentwise, reusing the factor bicone data and
`Prod.hom_ext` for all component equalities.

Nonclaims: no `ExactCategory (C × D)`, no biproduct functor, no Waldhausen
structure, no additivity theorem, no K-theory or G-theory content.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
variable (A : Type u₃) [Category.{v₃} A] [Preadditive A]

/-- Componentwise preadditive structure on a product of preadditive categories. -/
instance prodPreadditive : Preadditive (C × D) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))
  add_comp := fun X Y Z f f' g => by
    apply Prod.hom_ext
    · exact Preadditive.add_comp _ _ _ _ _ _
    · exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := fun X Y Z f g g' => by
    apply Prod.hom_ext
    · exact Preadditive.comp_add _ _ _ _ _ _
    · exact Preadditive.comp_add _ _ _ _ _ _

/-- The first projection from a product of preadditive categories is additive. -/
instance prodFstAdditive : (Prod.fst C D).Additive where
  map_add := fun {X Y f g} => by simp

/-- The second projection from a product of preadditive categories is additive. -/
instance prodSndAdditive : (Prod.snd C D).Additive where
  map_add := fun {X Y f g} => by simp

/-- Componentwise binary biproducts for a product of categories with biproducts. -/
instance prodHasBinaryBiproducts [HasBinaryBiproducts C] [HasBinaryBiproducts D] :
    HasBinaryBiproducts (C × D) where
  has_binary_biproduct P Q := by
    obtain ⟨dC⟩ :=
      (HasBinaryBiproducts.has_binary_biproduct P.1 Q.1).exists_binary_biproduct
    obtain ⟨dD⟩ :=
      (HasBinaryBiproducts.has_binary_biproduct P.2 Q.2).exists_binary_biproduct
    let bC := dC.bicone
    let bD := dD.bicone
    have hLimC : IsLimit bC.toCone := dC.isBilimit.isLimit
    have hLimD : IsLimit bD.toCone := dD.isBilimit.isLimit
    let b : BinaryBicone P Q :=
      { pt := (bC.pt, bD.pt)
        fst := (bC.fst, bD.fst)
        snd := (bC.snd, bD.snd)
        inl := (bC.inl, bD.inl)
        inr := (bC.inr, bD.inr)
        inl_fst := by
          apply Prod.hom_ext
          · exact bC.inl_fst
          · exact bD.inl_fst
        inl_snd := by
          apply Prod.hom_ext
          · exact bC.inl_snd
          · exact bD.inl_snd
        inr_fst := by
          apply Prod.hom_ext
          · exact bC.inr_fst
          · exact bD.inr_fst
        inr_snd := by
          apply Prod.hom_ext
          · exact bC.inr_snd
          · exact bD.inr_snd }
    have hLim : IsLimit b.toCone :=
      BinaryFan.IsLimit.mk _
        (fun {T} f g =>
          (BinaryFan.IsLimit.lift hLimC f.1 g.1,
            BinaryFan.IsLimit.lift hLimD f.2 g.2))
        (fun {T} f g => by
          apply Prod.hom_ext
          · exact BinaryFan.IsLimit.lift_fst hLimC f.1 g.1
          · exact BinaryFan.IsLimit.lift_fst hLimD f.2 g.2)
        (fun {T} f g => by
          apply Prod.hom_ext
          · exact BinaryFan.IsLimit.lift_snd hLimC f.1 g.1
          · exact BinaryFan.IsLimit.lift_snd hLimD f.2 g.2)
        (fun {T} f g m hm1 hm2 => by
          apply Prod.hom_ext
          · apply BinaryFan.IsLimit.hom_ext hLimC
            · rw [BinaryFan.IsLimit.lift_fst]
              exact congrArg (fun f => f.1) hm1
            · rw [BinaryFan.IsLimit.lift_snd]
              exact congrArg (fun f => f.1) hm2
          · apply BinaryFan.IsLimit.hom_ext hLimD
            · rw [BinaryFan.IsLimit.lift_fst]
              exact congrArg (fun f => f.2) hm1
            · rw [BinaryFan.IsLimit.lift_snd]
              exact congrArg (fun f => f.2) hm2)
    exact HasBinaryBiproduct.mk ⟨b, Limits.isBinaryBilimitOfIsLimit b hLim⟩

/-- Pairing of additive functors into a product is additive.

For additive `F : A ⥤ C` and `G : A ⥤ D`, the pairing `Functor.prod' F G`
preserves addition componentwise, reusing `Prod.hom_ext` and the product
preadditive structure.

Nonclaims: no exactness of the pairing, no diagonal/biproduct-functor exactness,
no Waldhausen additivity, no K-theory or G-theory, no realization, no spectra,
no Q/S comparison. -/
instance prodPairingAdditive (F : A ⥤ C) (G : A ⥤ D) [F.Additive] [G.Additive] :
    (F.prod' G).Additive where
  map_add := fun {X Y f g} => by
    apply Prod.hom_ext
    · change F.map (f + g) = F.map f + F.map g
      exact F.map_add
    · change G.map (f + g) = G.map f + G.map g
      exact G.map_add

end CategoryTheory
