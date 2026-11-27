/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality

/-!
# Naturality and inclusions for the simplicial join associator

This file records compatibility of the actual `SSet.joinAssocIso` with maps
in the left factor and with the canonical inclusions. The proofs use the
Day associator, the natural augmented join comparison, and the Day unitors.
No monoidal structure on simplicial sets is assumed.

The private computations of the augmented inclusions are adapted from
`MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet.Join

/-- The canonical map from the Day unit to an augmented simplicial set. -/
private def unitToAugDay (X : SSet.{u}) : 𝟙_ DayCat.{u} ⟶ augDay.obj X :=
  dayUnitYonedaIso.{u}.hom ≫ augDayBotIso.{u}.inv ≫ augDay.map (initial.to X)

private lemma augDay_map_joinInl (X Y : SSet.{u}) :
    augDay.map (joinInl X Y) ≫ (augDayJoinIso X Y).hom =
      (ρ_ (augDay.obj X)).inv ≫ (augDay.obj X ◁ unitToAugDay Y) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      simp only [joinInl]
      rw [join_obj_map_eq]
      simp only [joinBotIso, unitToAugDay, whiskerLeft_comp,
        DayFunctor.comp_natTrans, NatTrans.comp_app]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj X) (augDay.obj Y)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext

private lemma augDay_map_joinInr (X Y : SSet.{u}) :
    augDay.map (joinInr X Y) ≫ (augDayJoinIso X Y).hom =
      (λ_ (augDay.obj Y)).inv ≫ (unitToAugDay X ▷ augDay.obj Y) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      simp only [joinInr]
      rw [join_map_app_eq]
      simp only [botJoinIso, unitToAugDay, comp_whiskerRight,
        DayFunctor.comp_natTrans, NatTrans.comp_app]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj X) (augDay.obj Y)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext

end SSet.Join

namespace SSet

/-- The join associator is natural in the leftmost factor. -/
@[reassoc]
theorem joinAssocIso_naturality_left {X X' : SSet.{u}} (f : X ⟶ X')
    (Y Z : SSet.{u}) :
    (join.map ((join.map f).app Y)).app Z ≫ (joinAssocIso X' Y Z).hom =
      (joinAssocIso X Y Z).hom ≫ (join.map f).app (Y ⋆ Z) := by
  rw [join_map_app_eq ((join.map f).app Y), join_map_app_eq (Y := Y ⋆ Z) f]
  change Join.dropDay.map (Join.augDay.map ((join.map f).app Y) ▷ Join.augDay.obj Z) ≫
      Join.dropDay.map ((Join.augDayJoinIso X' Y).hom ▷ Join.augDay.obj Z ≫
        (α_ (Join.augDay.obj X') (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
        Join.augDay.obj X' ◁ (Join.augDayJoinIso Y Z).inv) =
    Join.dropDay.map ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
        (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
        Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv) ≫
      Join.dropDay.map (Join.augDay.map f ▷ Join.augDay.obj (Y ⋆ Z))
  simp only [← Functor.map_comp]
  congr 1
  rw [← comp_whiskerRight_assoc, Join.augDayJoinIso_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_left_assoc, ← whisker_exchange]
  simp only [Category.assoc]

/-- Including the right pair and then associating is the canonical right
inclusion of that pair. -/
@[reassoc]
theorem join_map_joinInr_comp_joinAssocIso_hom (X Y Z : SSet.{u}) :
    (join.map (joinInr X Y)).app Z ≫ (joinAssocIso X Y Z).hom =
      joinInr X (Y ⋆ Z) := by
  have hday :
      (Join.augDay.map (joinInr X Y) ▷ Join.augDay.obj Z) ≫
          (Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
          (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
          Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv =
        (Join.augDayJoinIso Y Z).inv ≫ Join.augDay.map (joinInr X (Y ⋆ Z)) ≫
          (Join.augDayJoinIso X (Y ⋆ Z)).hom := by
    rw [Join.augDay_map_joinInr]
    rw [← comp_whiskerRight_assoc, Join.augDay_map_joinInr,
      comp_whiskerRight_assoc, associator_naturality_left_assoc,
      ← leftUnitor_tensor_inv_assoc, ← whisker_exchange,
      ← leftUnitor_inv_naturality_assoc]
  rw [join_map_app_eq (joinInr X Y)]
  apply NatTrans.ext
  funext n
  apply TypeCat.homEquiv.injective
  funext z
  -- The augmented join comparison is the identity in every simplicial degree.
  exact types_congr_hom (NatTrans.congr_app (congrArg Join.dropDay.map hday) n) z

/-- The rightmost inclusion is unchanged by the join associator. -/
@[reassoc]
theorem joinInr_comp_joinAssocIso_hom (X Y Z : SSet.{u}) :
    joinInr (X ⋆ Y) Z ≫ (joinAssocIso X Y Z).hom =
      joinInr Y Z ≫ joinInr X (Y ⋆ Z) := by
  rw [← joinInr_comp_map (joinInr X Y) Z, Category.assoc,
    join_map_joinInr_comp_joinAssocIso_hom]

/-- Including the left factor and skipping the middle factor agrees with
the right inclusion in the right pair after associating. -/
@[reassoc]
theorem join_map_joinInl_comp_joinAssocIso_hom (X Y Z : SSet.{u}) :
    (join.map (joinInl X Y)).app Z ≫ (joinAssocIso X Y Z).hom =
      (join.obj X).map (joinInr Y Z) := by
  rw [join_map_app_eq (joinInl X Y), join_obj_map_eq X (joinInr Y Z)]
  change Join.dropDay.map (Join.augDay.map (joinInl X Y) ▷ Join.augDay.obj Z) ≫
      Join.dropDay.map ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
        (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
        Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv) =
    Join.dropDay.map (Join.augDay.obj X ◁ Join.augDay.map (joinInr Y Z))
  simp only [← Functor.map_comp]
  congr 1
  rw [← comp_whiskerRight_assoc, Join.augDay_map_joinInl,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc,
    triangle_assoc_comp_right_inv_assoc, ← whiskerLeft_comp_assoc,
    ← Join.augDay_map_joinInr]
  rw [whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv, Category.comp_id]

end SSet

namespace SSet

/-- The Day join associator is natural in the original rightmost factor. -/
@[reassoc]
theorem joinAssocIso_naturality_right (X Y : SSet.{u}) {Z Z' : SSet.{u}}
    (f : Z ⟶ Z') :
    (join.obj (X ⋆ Y)).map f ≫ (joinAssocIso X Y Z').hom =
      (joinAssocIso X Y Z).hom ≫ (join.obj X).map ((join.obj Y).map f) := by
  have hi : (Join.augDay.obj Y ◁ Join.augDay.map f) ≫
        (Join.augDayJoinIso Y Z').inv =
      (Join.augDayJoinIso Y Z).inv ≫ Join.augDay.map ((join.obj Y).map f) := by
    apply (cancel_epi (Join.augDayJoinIso Y Z).hom).mp
    calc
      (Join.augDayJoinIso Y Z).hom ≫
          ((Join.augDay.obj Y ◁ Join.augDay.map f) ≫ (Join.augDayJoinIso Y Z').inv) =
        ((Join.augDayJoinIso Y Z).hom ≫ (Join.augDay.obj Y ◁ Join.augDay.map f)) ≫
          (Join.augDayJoinIso Y Z').inv := (Category.assoc _ _ _).symm
      _ = (Join.augDay.map ((join.obj Y).map f) ≫ (Join.augDayJoinIso Y Z').hom) ≫
          (Join.augDayJoinIso Y Z').inv := by rw [← Join.augDayJoinIso_naturality_right]
      _ = Join.augDay.map ((join.obj Y).map f) := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (Join.augDayJoinIso Y Z).hom ≫
          ((Join.augDayJoinIso Y Z).inv ≫ Join.augDay.map ((join.obj Y).map f)) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [join_obj_map_eq (X ⋆ Y) f, join_obj_map_eq X ((join.obj Y).map f)]
  change Join.dropDay.map (Join.augDay.obj (X ⋆ Y) ◁ Join.augDay.map f) ≫
      Join.dropDay.map ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z' ≫
        (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z')).hom ≫
        Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z').inv) =
    Join.dropDay.map ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
      (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
      Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv) ≫
        Join.dropDay.map (Join.augDay.obj X ◁ Join.augDay.map ((join.obj Y).map f))
  simp only [← Functor.map_comp]
  congr 1
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp, hi, whiskerLeft_comp]
  simp only [Category.assoc]

/-- The original left pair inclusion is retained by the actual join associator. -/
@[reassoc]
theorem joinInl_pair_comp_joinAssocIso_hom (X Y Z : SSet.{u}) :
    joinInl (X ⋆ Y) Z ≫ (joinAssocIso X Y Z).hom =
      (join.obj X).map (joinInl Y Z) := by
  have hday :
      ((ρ_ (Join.augDay.obj (X ⋆ Y))).inv ≫
        (Join.augDay.obj (X ⋆ Y) ◁ Join.unitToAugDay Z)) ≫
        ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
          (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
          Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv) =
      (Join.augDayJoinIso X Y).hom ≫
        (Join.augDay.obj X ◁ Join.augDay.map (joinInl Y Z)) := by
    rw [Category.assoc, whisker_exchange_assoc,
      ← rightUnitor_inv_naturality_assoc, associator_naturality_right_assoc,
      rightUnitor_tensor_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, ← Join.augDay_map_joinInl]
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv, Category.comp_id]
  have hid : Join.dropDay.map (Join.augDayJoinIso X Y).hom = 𝟙 (X ⋆ Y) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  have hin : joinInl (X ⋆ Y) Z = Join.dropDay.map
      ((ρ_ (Join.augDay.obj (X ⋆ Y))).inv ≫
        (Join.augDay.obj (X ⋆ Y) ◁ Join.dayUnitYonedaIso.hom) ≫
        (Join.augDay.obj (X ⋆ Y) ◁ Join.augDayBotIso.inv) ≫
        (Join.augDay.obj (X ⋆ Y) ◁ Join.augDay.map (initial.to Z))) := by
    simp only [SSet.joinInl, SSet.joinBotIso, SSet.join_obj_map_eq,
      Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
      id_tensorHom, Functor.map_comp, Category.assoc]
    rfl
  rw [hin, join_obj_map_eq X (joinInl Y Z)]
  rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  change Join.dropDay.map ((ρ_ (Join.augDay.obj (X ⋆ Y))).inv ≫
      (Join.augDay.obj (X ⋆ Y) ◁ Join.unitToAugDay Z)) ≫
      Join.dropDay.map ((Join.augDayJoinIso X Y).hom ▷ Join.augDay.obj Z ≫
        (α_ (Join.augDay.obj X) (Join.augDay.obj Y) (Join.augDay.obj Z)).hom ≫
        Join.augDay.obj X ◁ (Join.augDayJoinIso Y Z).inv) =
    Join.dropDay.map (Join.augDay.obj X ◁ Join.augDay.map (joinInl Y Z))
  rw [← Functor.map_comp, hday, Functor.map_comp, hid]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- The original leftmost inclusion is retained by the entire join associator. -/
@[reassoc]
theorem joinInl_comp_joinAssocIso_hom (X Y Z : SSet.{u}) :
    joinInl X Y ≫ joinInl (X ⋆ Y) Z ≫ (joinAssocIso X Y Z).hom =
      joinInl X (Y ⋆ Z) := by
  rw [← Category.assoc, map_comp_joinInl, Category.assoc,
    join_map_joinInl_comp_joinAssocIso_hom, joinInl_comp_map]

end SSet
