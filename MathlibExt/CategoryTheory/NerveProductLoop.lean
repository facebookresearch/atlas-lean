/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveProduct
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# The whole product nerve cylinder of a constant second loop

A constant second-object endomorphism gives a natural endomorphism of the
actual first-factor inclusion. Its full nerve cylinder is the original
first simplex paired with the Yoneda simplex of that original loop edge.
The equation is retained after EVERY product-category functor.

This is a whole simplicial-map equality, not merely a statement about the
trace at a selected vertex or about its fundamental-group class.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial CategoryTheory.Prod

universe u v

namespace CategoryTheory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]

/-- The original second loop gives a whole natural endomorphism of that
first-factor inclusion; the active arrow remains its identity. -/
public def productConstantLoop (d : D) (k : d ⟶ d) :
    Prod.sectL C d ⟶ Prod.sectL C d where
  app c := (𝟙 c) ×ₘ k
  naturality c c' p := by
    change (p ≫ 𝟙 c', (𝟙 d) ≫ k) = ((𝟙 c) ≫ p, k ≫ 𝟙 d)
    simp only [Category.comp_id, Category.id_comp]

private theorem productConstantLoop_app_computed (d : D) (k : d ⟶ d) (c : C) :
    (productConstantLoop C D d k).app c = (𝟙 c) ×ₘ k := rfl

/-- The complete loop transformation retains the original active identity
and the SAME inactive arrow at every object. -/
public theorem productConstantLoop_app (d : D) (k : d ⟶ d) (c : C) :
    (productConstantLoop C D d k).app c = (𝟙 c) ×ₘ k :=
  productConstantLoop_app_computed C D d k c

private theorem productConstantLoop_cylinder (d : D) (k : d ⟶ d) :
    NatTrans.nerveCylinderFunctor (productConstantLoop C D d k) =
      (Prod.fst C (Fin 2)).prod'
        ((Prod.snd C (Fin 2)) ⋙ ComposableArrows.mk₁ k) := by
  apply Functor.hext
  · rintro ⟨c, t⟩
    fin_cases t <;> rfl
  · rintro ⟨c, t⟩ ⟨c', t'⟩ p
    rcases p with ⟨p, q⟩
    fin_cases t
    · fin_cases t'
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, productConstantLoop,
          Prod.sectL, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, productConstantLoop,
          Prod.sectL, ComposableArrows.mk₁]
    · fin_cases t'
      · exfalso
        have hle : (1 : Fin 2) ≤ 0 := leOfHom q
        omega
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, productConstantLoop,
          Prod.sectL, ComposableArrows.mk₁]

/-- The ENTIRE original loop cylinder is the strict nerve-product pair
of the original active simplex and the original loop-edge simplex. -/
public theorem nerveHomotopyMap_productConstantLoop (d : D) (k : d ⟶ d) :
    NatTrans.nerveHomotopyMap (productConstantLoop C D d k) ≫
        (nerveProdIso C D).hom =
      Limits.prod.lift
        (CartesianMonoidalCategory.fst (nerve C) (Δ[1] : SSet.{max u v}))
        (CartesianMonoidalCategory.snd (nerve C) (Δ[1] : SSet.{max u v}) ≫
          SSet.yonedaEquiv.symm (nerve.edgeMk k).edge) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, nerveProdIso_hom_comp_fst, Limits.prod.lift_fst]
    ext Δ x
    change (((NatTrans.nerveCylinderFunctor (productConstantLoop C D d k)).mapComposableArrows
      Δ.unop.len).obj (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)) ⋙
      Prod.fst C D = x.1
    rw [productConstantLoop_cylinder]
    rfl
  · rw [Category.assoc, nerveProdIso_hom_comp_snd, Limits.prod.lift_snd]
    ext Δ x
    change (((NatTrans.nerveCylinderFunctor (productConstantLoop C D d k)).mapComposableArrows
      Δ.unop.len).obj (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)) ⋙
      Prod.snd C D = (SSet.yonedaEquiv.symm (nerve.edgeMk k).edge).app Δ x.2
    rw [productConstantLoop_cylinder]
    rfl

variable {E : Type u} [Category.{v} E]

/-- Postcomposition keeps the whole original product-family loop map,
including every active simplex and the SAME original inactive edge. -/
public theorem nerveHomotopyMap_productConstantLoop_postcomp
    (d : D) (k : d ⟶ d) (F : C × D ⥤ E) :
    NatTrans.nerveHomotopyMap
        (Functor.whiskerRight (productConstantLoop C D d k) F) =
      Limits.prod.lift
        (CartesianMonoidalCategory.fst (nerve C) (Δ[1] : SSet.{max u v}))
        (CartesianMonoidalCategory.snd (nerve C) (Δ[1] : SSet.{max u v}) ≫
          SSet.yonedaEquiv.symm (nerve.edgeMk k).edge) ≫
            (nerveProdIso C D).inv ≫ nerveMap F := by
  have hpair : NatTrans.nerveHomotopyMap (productConstantLoop C D d k) =
      Limits.prod.lift
        (CartesianMonoidalCategory.fst (nerve C) (Δ[1] : SSet.{max u v}))
        (CartesianMonoidalCategory.snd (nerve C) (Δ[1] : SSet.{max u v}) ≫
          SSet.yonedaEquiv.symm (nerve.edgeMk k).edge) ≫ (nerveProdIso C D).inv := by
    apply (cancel_mono (nerveProdIso C D).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      nerveHomotopyMap_productConstantLoop C D d k
  rw [← NatTrans.nerveHomotopyMap_postcomp, hpair, Category.assoc]

end CategoryTheory

end
