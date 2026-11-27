/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Ordinary monoidal data projected from genuine enriched functors

The full enriched tensor naturality, identities and composition imply the
ordinary functor and tensor naturality. The input is genuine enriched
monoidal data; no additional ordinary law is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC vC uD vD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [EnrichedOrdinaryCategory V C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [EnrichedOrdinaryCategory V D]

/-- Genuine enriched tensor naturality implies naturality for every ordinary arrow pair. -/
theorem inducedOrdinary_mu_naturality
    (dC : EnrichedMonoidalCategoryData V C) (dD : EnrichedMonoidalCategoryData V D)
    (F : EnrichedFunctor V C D) (L : LaxMonoidalData dC dD F)
    {X Y A B : C} (f : X ⟶ Y) (g : A ⟶ B) :
    (F.toOrdinaryFunctor.map f ⊗ₘ F.toOrdinaryFunctor.map g) ≫ L.mu Y B =
      L.mu X A ≫ F.toOrdinaryFunctor.map (f ⊗ₘ g) := by
  let p : 𝟙_ V ⟶ (X ⟶[V] Y) ⊗ (A ⟶[V] B) :=
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g)
  let a := F.map X Y ⊗ₘ F.map A B
  let b := dD.tensorMap (F.obj X) (F.obj Y) (F.obj A) (F.obj B)
  let w := eHomWhiskerLeft V (F.obj X ⊗ F.obj A) (L.mu Y B)
  let c := dC.tensorMap X Y A B
  let t := F.map (X ⊗ A) (Y ⊗ B)
  let z := eHomWhiskerRight V (L.mu X A) (F.obj (Y ⊗ B))
  have h := congrArg (fun k => p ≫ k) (L.mu_naturality X Y A B)
  have ha : p ≫ a = (λ_ (𝟙_ V)).inv ≫
      (eHomEquiv V (F.toOrdinaryFunctor.map f) ⊗ₘ eHomEquiv V (F.toOrdinaryFunctor.map g)) := by
    dsimp only [p, a]
    rw [Category.assoc, tensorHom_comp_tensorHom,
      ← toOrdinaryFunctor_map, ← toOrdinaryFunctor_map]
    rfl
  have hb : p ≫ a ≫ b = eHomEquiv V (F.toOrdinaryFunctor.map f ⊗ₘ F.toOrdinaryFunctor.map g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ b) ha).trans
        (by simpa only [Category.assoc, toOrdinaryFunctor_obj, b] using
          dD.tensorMap_eHomEquiv (F.toOrdinaryFunctor.map f) (F.toOrdinaryFunctor.map g)))
  have hc : p ≫ c = eHomEquiv V (f ⊗ₘ g) := by
    simpa only [p, c, Category.assoc] using dC.tensorMap_eHomEquiv f g
  have ht : p ≫ c ≫ t = eHomEquiv V (F.toOrdinaryFunctor.map (f ⊗ₘ g)) :=
    (Category.assoc p c t).symm.trans
      ((congrArg (fun k => k ≫ t) hc).trans (toOrdinaryFunctor_map F (f ⊗ₘ g)).symm)
  have hL : p ≫ a ≫ b ≫ w =
      eHomEquiv V ((F.toOrdinaryFunctor.map f ⊗ₘ F.toOrdinaryFunctor.map g) ≫ L.mu Y B) :=
    (congrArg (fun k => p ≫ k) (Category.assoc a b w).symm).trans
      ((Category.assoc p (a ≫ b) w).symm.trans
      ((congrArg (fun k => k ≫ w) hb).trans
        (eHomEquiv_comp_eHomWhiskerLeft V D _ _)))
  have hR : p ≫ c ≫ t ≫ z =
      eHomEquiv V (L.mu X A ≫ F.toOrdinaryFunctor.map (f ⊗ₘ g)) :=
    (congrArg (fun k => p ≫ k) (Category.assoc c t z).symm).trans
      ((Category.assoc p (c ≫ t) z).symm.trans
      ((congrArg (fun k => k ≫ z) ht).trans
        (eHomEquiv_comp_eHomWhiskerRight V D _ _)))
  apply (eHomEquiv V).injective
  exact hL.symm.trans (h.trans hR)

/-- The original enriched monoidal unit/tensor/associativity yield ordinary lax monoidal data. -/
@[instance_reducible]
def inducedOrdinaryLaxMonoidal
    (dC : EnrichedMonoidalCategoryData V C) (dD : EnrichedMonoidalCategoryData V D)
    (F : EnrichedFunctor V C D) (L : LaxMonoidalData dC dD F) :
    (F.toOrdinaryFunctor).LaxMonoidal := by
  have hmap {X Y : C} (f : X ⟶ Y) :
      F.toOrdinaryFunctor.map f = (eHomEquiv V).symm (eHomEquiv V f ≫ F.map X Y) := rfl
  exact Functor.LaxMonoidal.ofTensorHom (F := F.toOrdinaryFunctor) L.epsilon L.mu
    (inducedOrdinary_mu_naturality dC dD F L)
    (fun X Y Z => by
      simpa only [toOrdinaryFunctor_obj, hmap, tensorHom_id, id_tensorHom]
        using L.assoc X Y Z)
    (fun X => by
      simpa only [toOrdinaryFunctor_obj, hmap, tensorHom_id] using (L.unit X).1)
    (fun X => by
      simpa only [toOrdinaryFunctor_obj, hmap, id_tensorHom] using (L.unit X).2)

end CategoryTheory.EnrichedFunctor
