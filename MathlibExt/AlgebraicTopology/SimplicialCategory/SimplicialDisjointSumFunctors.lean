/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialDisjointSum

/-!
# The actual disjoint-sum enriched maps and full original coproduct bijection

Both original object families and their entire Hom maps are retained.
The actual sum descender acts by each supplied original whole enriched
functor on its own family. Both full original injection equations and
uniqueness follow on those SAME objects and every original coefficient.
Source, target and common codomain object universes remain independent.
-/

noncomputable section
universe u v w t
open CategoryTheory MonoidalCategory

namespace SSet.DisjointSum
attribute [local instance] enrichment

variable (C : Type v) (D : Type w) [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]

/-- The original left family includes with its SAME objects and identity full Hom maps. -/
def inl : EnrichedFunctor SSet.{u} C (C ⊕ D) where
  obj := Sum.inl
  map _x _y := 𝟙 _
  map_id _x := Category.comp_id _
  map_comp x y z := by
    change eComp SSet.{u} x y z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet.{u} x y z
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- The original right family includes with its SAME objects and identity full Hom maps. -/
def inr : EnrichedFunctor SSet.{u} D (C ⊕ D) where
  obj := Sum.inr
  map _x _y := 𝟙 _
  map_id _x := Category.comp_id _
  map_comp x y z := by
    change eComp SSet.{u} x y z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet.{u} x y z
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    rfl

variable {C D} {E : Type t} [EnrichedCategory SSet.{u} E]

private def fromEmpty (X : SSet.{u}) : WalkingHom.emptyHom ⟶ X where
  app _q := ↾PEmpty.elim
  naturality _q _r _f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p

/-- Evaluate each SAME original object family by its own supplied complete enriched functor. -/
def desc (F : EnrichedFunctor SSet.{u} C E) (G : EnrichedFunctor SSet.{u} D E) :
    EnrichedFunctor SSet.{u} (C ⊕ D) E where
  obj := Sum.elim F.obj G.obj
  map x y := match x, y with
    | .inl x, .inl y => F.map x y
    | .inl x, .inr y => fromEmpty (F.obj x ⟶[SSet.{u}] G.obj y)
    | .inr x, .inl y => fromEmpty (G.obj x ⟶[SSet.{u}] F.obj y)
    | .inr x, .inr y => G.map x y
  map_id x := by
    cases x with
    | inl x => exact F.map_id x
    | inr x => exact G.map_id x
  map_comp x y z := by
    cases x <;> cases y <;> cases z
    case inl.inl.inl x y z => exact F.map_comp x y z
    case inr.inr.inr x y z => exact G.map_comp x y z
    all_goals
      apply NatTrans.ext
      funext q
      apply ConcreteCategory.hom_ext
      intro p
      first
        | exact PEmpty.elim p.1
        | exact PEmpty.elim p.2

/-- The actual full sum descender retains the SAME supplied whole left functor. -/
theorem inl_desc (F : EnrichedFunctor SSet.{u} C E) (G : EnrichedFunctor SSet.{u} D E) :
    (inl C D).comp SSet.{u} (desc F G) = F := by
  apply EnrichedFunctor.ext SSet.{u} (fun _x => rfl)
  intro x y
  change (𝟙 _ ≫ F.map x y) ≫ 𝟙 _ = F.map x y
  simp only [Category.id_comp, Category.comp_id]

/-- The actual full sum descender retains the SAME supplied whole right functor. -/
theorem inr_desc (F : EnrichedFunctor SSet.{u} C E) (G : EnrichedFunctor SSet.{u} D E) :
    (inr C D).comp SSet.{u} (desc F G) = G := by
  apply EnrichedFunctor.ext SSet.{u} (fun _x => rfl)
  intro x y
  change (𝟙 _ ≫ G.map x y) ≫ 𝟙 _ = G.map x y
  simp only [Category.id_comp, Category.comp_id]

/-- Both original family restrictions reconstruct the SAME complete enriched sum functor. -/
theorem desc_readback (H : EnrichedFunctor SSet.{u} (C ⊕ D) E) :
    desc ((inl C D).comp SSet.{u} H) ((inr C D).comp SSet.{u} H) = H := by
  apply EnrichedFunctor.ext SSet.{u} (fun x => by cases x <;> rfl)
  intro x y
  cases x <;> cases y
  case inl.inl x y =>
    change (𝟙 _ ≫ H.map (Sum.inl x) (Sum.inl y)) ≫ 𝟙 _ = H.map (Sum.inl x) (Sum.inl y)
    simp only [Category.id_comp, Category.comp_id]
  case inr.inr x y =>
    change (𝟙 _ ≫ H.map (Sum.inr x) (Sum.inr y)) ≫ 𝟙 _ = H.map (Sum.inr x) (Sum.inr y)
    simp only [Category.id_comp, Category.comp_id]
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p

/-- The entire original enriched sum map is determined by its SAME two full family restrictions. -/
theorem desc_unique (F : EnrichedFunctor SSet.{u} C E) (G : EnrichedFunctor SSet.{u} D E)
    (H : EnrichedFunctor SSet.{u} (C ⊕ D) E)
    (hF : (inl C D).comp SSet.{u} H = F) (hG : (inr C D).comp SSet.{u} H = G) :
    H = desc F G := by
  rw [← hF, ← hG]
  exact (desc_readback H).symm

/-- Actual full enriched functors out of the SAME disjoint sum are exactly the two original whole family functors. -/
def functorEquiv : EnrichedFunctor SSet.{u} (C ⊕ D) E ≃
    EnrichedFunctor SSet.{u} C E × EnrichedFunctor SSet.{u} D E where
  toFun H := ⟨(inl C D).comp SSet.{u} H, (inr C D).comp SSet.{u} H⟩
  invFun p := desc p.1 p.2
  left_inv := desc_readback
  right_inv p := Prod.ext (inl_desc p.1 p.2) (inr_desc p.1 p.2)

end SSet.DisjointSum
