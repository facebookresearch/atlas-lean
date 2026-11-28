/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Strict enriched composition and precomposition by actual inverse functors

The full enriched functor composition has the original associative
and unit equalities, beyond its ordinary natural comparison maps.
Two specified strict inverse functors therefore induce an actual
bijection on whole enriched functors by precomposition.
-/

@[expose] public section

noncomputable section

universe v w u₁ u₂ u₃ u₄

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
  {C : Type u₁} [EnrichedCategory V C] {D : Type u₂} [EnrichedCategory V D]
  {E : Type u₃} [EnrichedCategory V E] {K : Type u₄} [EnrichedCategory V K]

private theorem map_heq_objects (F : EnrichedFunctor V C D) {x x' y y' : C}
    (hx : x = x') (hy : y = y') : F.map x y ≍ F.map x' y' := by
  cases hx
  cases hy
  rfl

/-- The whole original enriched composition is strictly associative. -/
theorem comp_assoc_eq (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    (H : EnrichedFunctor V E K) :
    comp V (comp V F G) H = comp V F (comp V G H) := by
  apply EnrichedFunctor.ext V (F := comp V (comp V F G) H) (G := comp V F (comp V G H))
    (fun _ => rfl)
  intro x y
  apply eq_of_heq
  rw [comp_eqToHom_heq_iff]
  have hx := comp_obj V F G x
  have hy := comp_obj V F G y
  have hm : ((comp V F G).obj x ⟶[V] (comp V F G).obj y) =
      (G.obj (F.obj x) ⟶[V] G.obj (F.obj y)) := congrArg₂ (fun x y : E => x ⟶[V] y) hx hy
  have ht : (H.obj ((comp V F G).obj x) ⟶[V] H.obj ((comp V F G).obj y)) =
      (H.obj (G.obj (F.obj x)) ⟶[V] H.obj (G.obj (F.obj y))) :=
    congrArg₂ (fun x y : K => x ⟶[V] y) (congrArg H.obj hx) (congrArg H.obj hy)
  have hl := (heq_of_eq (comp_map V (comp V F G) H x y)).trans
    (heq_comp rfl hm ht (heq_of_eq (comp_map V F G x y)) (map_heq_objects H hx hy))
  have htx := comp_obj V G H (F.obj x)
  have hty := comp_obj V G H (F.obj y)
  have htr : ((comp V G H).obj (F.obj x) ⟶[V] (comp V G H).obj (F.obj y)) =
      (H.obj (G.obj (F.obj x)) ⟶[V] H.obj (G.obj (F.obj y))) :=
    congrArg₂ (fun x y : K => x ⟶[V] y) htx hty
  have hr := (heq_of_eq (comp_map V F (comp V G H) x y)).trans
    (heq_comp rfl rfl htr (HEq.rfl : F.map x y ≍ F.map x y)
      (heq_of_eq (comp_map V G H (F.obj x) (F.obj y))))
  exact hl.trans ((heq_of_eq (Category.assoc (F.map x y) (G.map (F.obj x) (F.obj y))
    (H.map (G.obj (F.obj x)) (G.obj (F.obj y))))).trans hr.symm)

/-- The original identity on the source retains the entire enriched functor. -/
theorem id_comp_eq (F : EnrichedFunctor V C D) : comp V (id V C) F = F := by
  apply EnrichedFunctor.ext V (F := comp V (id V C) F) (G := F) (fun _ => rfl)
  intro x y
  apply eq_of_heq
  rw [comp_eqToHom_heq_iff]
  have hx := id_obj V C x
  have hy := id_obj V C y
  have hm : ((id V C).obj x ⟶[V] (id V C).obj y) = (x ⟶[V] y) :=
    congrArg₂ (fun x y : C => x ⟶[V] y) hx hy
  have ht : (F.obj ((id V C).obj x) ⟶[V] F.obj ((id V C).obj y)) = (F.obj x ⟶[V] F.obj y) :=
    congrArg₂ (fun x y : D => x ⟶[V] y) (congrArg F.obj hx) (congrArg F.obj hy)
  exact (heq_of_eq (comp_map V (id V C) F x y)).trans
    ((heq_comp rfl hm ht (heq_of_eq (id_map V C x y)) (map_heq_objects F hx hy)).trans
      (heq_of_eq (Category.id_comp (F.map x y))))

/-- The original identity on the target retains the entire enriched functor. -/
theorem comp_id_eq (F : EnrichedFunctor V C D) : comp V F (id V D) = F := by
  apply EnrichedFunctor.ext V (F := comp V F (id V D)) (G := F) (fun _ => rfl)
  intro x y
  apply eq_of_heq
  rw [comp_eqToHom_heq_iff]
  have hx := id_obj V D (F.obj x)
  have hy := id_obj V D (F.obj y)
  have ht : ((id V D).obj (F.obj x) ⟶[V] (id V D).obj (F.obj y)) = (F.obj x ⟶[V] F.obj y) :=
    congrArg₂ (fun x y : D => x ⟶[V] y) hx hy
  exact (heq_of_eq (comp_map V F (id V D) x y)).trans
    ((heq_comp rfl rfl ht (HEq.rfl : F.map x y ≍ F.map x y)
      (heq_of_eq (id_map V D (F.obj x) (F.obj y)))).trans
      (heq_of_eq (Category.comp_id (F.map x y))))

/-- Specified actual strict inverse functors give both whole precomposition inverse maps. -/
def precompEquiv (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D C)
    (hFG : comp V F G = id V C) (hGF : comp V G F = id V D) :
    EnrichedFunctor V D E ≃ EnrichedFunctor V C E where
  toFun H := comp V F H
  invFun H := comp V G H
  left_inv H :=
    (comp_assoc_eq G F H).symm.trans
      ((congrArg (fun J => comp V J H) hGF).trans (id_comp_eq H))
  right_inv H :=
    (comp_assoc_eq F G H).symm.trans
      ((congrArg (fun J => comp V J H) hFG).trans (id_comp_eq H))

end CategoryTheory.EnrichedFunctor
