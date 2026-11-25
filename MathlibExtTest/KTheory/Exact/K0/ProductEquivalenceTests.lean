/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.KTheory.Exact.K0.ProductEquivalence

/-!
# Original-map clients for the exact-category K₀ product

The category object and Hom universes are independent. The clients retain
the original projection programs and actual zero-functor object images.
Both inverse identities are tested on arbitrary elements of the whole groups.
-/

open CategoryTheory Limits ZeroObject AlgebraicKTheory

noncomputable section

universe v₁ u₁ v₂ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

example : K0 (C × D) ≃+ K0 C × K0 D := K0.prodEquiv C D

example : K0.prodFstInclusionFunctor C D = (𝟭 C).prod' (0 : C ⥤ D) := rfl

example : K0.prodSndInclusionFunctor C D = (0 : D ⥤ C).prod' (𝟭 D) := rfl

example : ((𝟭 C).prod' (0 : C ⥤ D)).IsExact :=
  K0.prodFstInclusionFunctorIsExact C D

example : ((0 : D ⥤ C).prod' (𝟭 D)).IsExact :=
  K0.prodSndInclusionFunctorIsExact C D

example :
    (K0.prodEquiv C D).toAddMonoidHom =
      (K0.map (CategoryTheory.Prod.fst C D)).prod
        (K0.map (CategoryTheory.Prod.snd C D)) := rfl

example (X : C) (Y : D) :
    K0.prodEquiv C D (K0.mk (X, Y)) = (K0.mk X, K0.mk Y) :=
  K0.prodEquiv_mk C D (X, Y)

example (X : C) :
    K0.prodFstInclusionHom C D (K0.mk X) =
      K0.mk (X, (0 : C ⥤ D).obj X) :=
  K0.prodFstInclusionHom_mk C D X

example (Y : D) :
    K0.prodSndInclusionHom C D (K0.mk Y) =
      K0.mk ((0 : D ⥤ C).obj Y, Y) :=
  K0.prodSndInclusionHom_mk C D Y

example (X : C) (Y : D) :
    (K0.prodEquiv C D).symm (K0.mk X, K0.mk Y) = K0.mk (X, Y) :=
  K0.prodEquiv_symm_mk C D X Y

example (a : K0 C) :
    K0.map (CategoryTheory.Prod.fst C D) (K0.prodFstInclusionHom C D a) = a :=
  DFunLike.congr_fun (K0.prodFstHom_comp_prodFstInclusionHom C D) a

example (a : K0 C) :
    K0.map (CategoryTheory.Prod.snd C D) (K0.prodFstInclusionHom C D a) = 0 :=
  DFunLike.congr_fun (K0.prodSndHom_comp_prodFstInclusionHom C D) a

example (b : K0 D) :
    K0.map (CategoryTheory.Prod.fst C D) (K0.prodSndInclusionHom C D b) = 0 :=
  DFunLike.congr_fun (K0.prodFstHom_comp_prodSndInclusionHom C D) b

example (b : K0 D) :
    K0.map (CategoryTheory.Prod.snd C D) (K0.prodSndInclusionHom C D b) = b :=
  DFunLike.congr_fun (K0.prodSndHom_comp_prodSndInclusionHom C D) b

example (z : K0 (C × D)) :
    K0.prodInverseHom C D
      (K0.map (CategoryTheory.Prod.fst C D) z,
        K0.map (CategoryTheory.Prod.snd C D) z) = z :=
  DFunLike.congr_fun (K0.prodInverseHom_comp_prodForwardHom C D) z

example (a : K0 C) (b : K0 D) :
    (K0.map (CategoryTheory.Prod.fst C D)
        (K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b),
      K0.map (CategoryTheory.Prod.snd C D)
        (K0.prodFstInclusionHom C D a + K0.prodSndInclusionHom C D b)) = (a, b) :=
  DFunLike.congr_fun (K0.prodForwardHom_comp_prodInverseHom C D) (a, b)

example (z : K0 (C × D)) :
    (K0.prodEquiv C D).symm (K0.prodEquiv C D z) = z :=
  (K0.prodEquiv C D).symm_apply_apply z

example (a : K0 C) (b : K0 D) :
    K0.prodEquiv C D ((K0.prodEquiv C D).symm (a, b)) = (a, b) :=
  (K0.prodEquiv C D).apply_symm_apply (a, b)

example : (K0.prodEquiv C D).symm (0, 0) = 0 := map_zero _

#print axioms AlgebraicKTheory.K0.prodEquiv
#print axioms AlgebraicKTheory.K0.prodInverseHom_comp_prodForwardHom
#print axioms AlgebraicKTheory.K0.prodForwardHom_comp_prodInverseHom
#print axioms AlgebraicKTheory.K0.prodEquiv_symm_mk
