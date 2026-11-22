/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialDisjointSumFunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# The SAME full disjoint-sum maps preserve every original Hom weak map

The four original object universes and coefficient universe are
independent. Each family has its SAME full original Hom map; crossing
Homs are the canonical empty coefficient object with its actual
identity map. No fibrancy or cofibrancy is required.
-/

noncomputable section
universe u v₁ w₁ v₂ w₂
open CategoryTheory

namespace SSet.DisjointSum
attribute [local instance] enrichment

variable {C : Type v₁} {D : Type w₁} {E : Type v₂} {K : Type w₂}
  [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  [EnrichedCategory SSet.{u} E] [EnrichedCategory SSet.{u} K]
  (F : EnrichedFunctor SSet.{u} C E) (G : EnrichedFunctor SSet.{u} D K)

/-- The SAME two complete original enriched functors on their actual disjoint families. -/
def map : EnrichedFunctor SSet.{u} (C ⊕ D) (E ⊕ K) :=
  desc (F.comp SSet.{u} (inl E K)) (G.comp SSet.{u} (inr E K))

/-- Each SAME original left object has its prescribed original left image. -/
theorem map_obj_inl (x : C) : (map F G).obj (Sum.inl x) = Sum.inl (F.obj x) := rfl

/-- Each SAME original right object has its prescribed original right image. -/
theorem map_obj_inr (x : D) : (map F G).obj (Sum.inr x) = Sum.inr (G.obj x) := rfl

/-- The full original left coefficient map is retained literally after the identity inclusion. -/
theorem map_hom_inl (x y : C) : (map F G).map (Sum.inl x) (Sum.inl y) = F.map x y :=
  Category.comp_id _

/-- The full original right coefficient map is retained literally after the identity inclusion. -/
theorem map_hom_inr (x y : D) : (map F G).map (Sum.inr x) (Sum.inr y) = G.map x y :=
  Category.comp_id _

/-- The actual left-to-right original empty Hom map is its full identity. -/
theorem map_hom_inl_inr (x : C) (y : D) :
    (map F G).map (Sum.inl x) (Sum.inr y) = 𝟙 WalkingHom.emptyHom := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  exact PEmpty.elim p

/-- The actual right-to-left original empty Hom map is its full identity. -/
theorem map_hom_inr_inl (x : D) (y : C) :
    (map F G).map (Sum.inr x) (Sum.inl y) = 𝟙 WalkingHom.emptyHom := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  exact PEmpty.elim p

/-- Every full original disjoint Hom map is weak from the SAME two original Hom weak hypotheses. -/
theorem map_local_weak (hF : ∀ x y : C, realizationWeakEquivalences (F.map x y))
    (hG : ∀ x y : D, realizationWeakEquivalences (G.map x y)) (x y : C ⊕ D) :
    realizationWeakEquivalences ((map F G).map x y) := by
  cases x <;> cases y
  case inl.inl x y =>
    exact (congrArg (fun f : (x ⟶[SSet.{u}] y) ⟶ (F.obj x ⟶[SSet.{u}] F.obj y) =>
      realizationWeakEquivalences f) (map_hom_inl F G x y)).mpr (hF x y)
  case inr.inr x y =>
    exact (congrArg (fun f : (x ⟶[SSet.{u}] y) ⟶ (G.obj x ⟶[SSet.{u}] G.obj y) =>
      realizationWeakEquivalences f) (map_hom_inr F G x y)).mpr (hG x y)
  case inl.inr x y =>
    exact (congrArg (fun f : WalkingHom.emptyHom.{u} ⟶ WalkingHom.emptyHom.{u} =>
      realizationWeakEquivalences f) (map_hom_inl_inr F G x y)).mpr
      (realizationWeakEquivalences.id_mem _)
  case inr.inl x y =>
    exact (congrArg (fun f : WalkingHom.emptyHom.{u} ⟶ WalkingHom.emptyHom.{u} =>
      realizationWeakEquivalences f) (map_hom_inr_inl F G x y)).mpr
      (realizationWeakEquivalences.id_mem _)

end SSet.DisjointSum
