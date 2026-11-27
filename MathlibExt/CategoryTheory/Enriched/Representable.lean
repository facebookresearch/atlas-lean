/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Enriched representable functors

The covariant representable in a monoidal closed base, and the contravariant
representable when the base is additionally braided, using the selected
closed self-enrichment.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite BraidedCategory

universe uV vV uA

namespace CategoryTheory.EnrichedFunctor

open scoped MonoidalClosed

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V]
variable (A : Type uA) [EnrichedCategory V A]

/-- The covariant enriched representable A(c, -). Its data stay reducible for anonymous
weighted-limit presentations. -/
abbrev covariantRepresentable (c : A) : EnrichedFunctor V A V where
  obj a := c ⟶[V] a
  map a b := MonoidalClosed.curry (eComp V c a b)
  map_id a := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry]
    rw [MonoidalClosed.enrichedCategorySelf_id,
      MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
    rw [← cancel_epi (ρ_ (c ⟶[V] a)).inv]
    simp
  map_comp a b d := by
    apply MonoidalClosed.uncurry_injective
    simp only [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry,
      MonoidalClosed.enrichedCategorySelf_comp,
      MonoidalClosed.comp_eq, MonoidalClosed.compTranspose_eq]
    have hTensor :
        (c ⟶[V] a) ◁
              (MonoidalClosed.curry (eComp V c a b) ⊗ₘ
                MonoidalClosed.curry (eComp V c b d)) ≫
            (α_ (c ⟶[V] a)
              ((ihom (c ⟶[V] a)).obj (c ⟶[V] b))
              ((ihom (c ⟶[V] b)).obj (c ⟶[V] d))).inv =
          (α_ (c ⟶[V] a) (a ⟶[V] b) (b ⟶[V] d)).inv ≫
            ((c ⟶[V] a) ◁ MonoidalClosed.curry (eComp V c a b)) ▷
              (b ⟶[V] d) ≫
            ((c ⟶[V] a) ⊗
                ((ihom (c ⟶[V] a)).obj (c ⟶[V] b))) ◁
              MonoidalClosed.curry (eComp V c b d) := by
      simpa only [id_tensorHom, tensorHom_def,
        MonoidalCategory.id_whiskerRight, Category.id_comp,
        comp_whiskerRight] using
        (associator_inv_naturality
          (𝟙 (c ⟶[V] a))
          (MonoidalClosed.curry (eComp V c a b))
          (MonoidalClosed.curry (eComp V c b d)))
    rw [← Category.assoc, hTensor]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
    rw [← comp_whiskerRight_assoc]
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    dsimp
    rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    exact (e_assoc V c a b d).symm

section Contravariant

variable [BraidedCategory V]

/-- The contravariant enriched representable A(-, c). -/
def contravariantRepresentable (c : A) : EnrichedFunctor V Aᵒᵖ V where
  obj a := a.unop ⟶[V] c
  map a b := MonoidalClosed.curry <|
    (β_ (a.unop ⟶[V] c) (b.unop ⟶[V] a.unop)).hom ≫
      eComp V b.unop a.unop c
  map_id a := by
    induction a using Opposite.rec with
    | _ a =>
      with_unfolding_all
        exact (covariantRepresentable V Aᵒᵖ (op c)).map_id (op a)
  map_comp a b d := by
    induction a using Opposite.rec with
    | _ a =>
      induction b using Opposite.rec with
      | _ b =>
        induction d using Opposite.rec with
        | _ d =>
          with_unfolding_all
            exact
              (covariantRepresentable V Aᵒᵖ (op c)).map_comp
                (op a) (op b) (op d)

end Contravariant

end CategoryTheory.EnrichedFunctor
