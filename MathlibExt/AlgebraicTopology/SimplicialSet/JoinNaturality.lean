/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinProperties

/-!
# Naturality and endpoint computations for simplicial joins

The augmented extension of a simplicial join is the Day tensor of the
augmented extensions of its factors.  This file records that comparison as a
natural isomorphism of bifunctors.  The componentwise naturality lemmas are
also exposed for constructions that work directly with Day tensor generators.

It also contains the standard-simplex naturality theorem in the right join
variable and the Day-convolution computation of the right endpoint inclusion
`joinInr`.  These neutral join calculations support mapping-space and
join--horn constructions without importing their specialized proof modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet.Join

/-- Naturality of `augDayJoinIso` in the left join factor. -/
lemma augDayJoinIso_naturality_left {X X' Y : SSet.{u}} (f : X ⟶ X') :
    augDay.map ((SSet.join.map f).app Y) ≫ (augDayJoinIso X' Y).hom =
      (augDayJoinIso X Y).hom ≫ (augDay.map f ▷ augDay.obj Y) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      rw [SSet.join_map_app_eq]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj X') (augDay.obj Y)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext

/-- Naturality of `augDayJoinIso` in the right join factor. -/
lemma augDayJoinIso_naturality_right {X Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    augDay.map ((SSet.join.obj X).map g) ≫ (augDayJoinIso X Y').hom =
      (augDayJoinIso X Y).hom ≫ (augDay.obj X ◁ augDay.map g) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      rw [SSet.join_obj_map_eq]
      rfl
  | star =>
      apply (isTerminalDayTensorFunctorObjStar (augDay.obj X) (augDay.obj Y')
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)
        (by rw [augDay_obj_functor, aug_obj_obj_star]; exact Types.isTerminalPUnit)).hom_ext

/-- Augmented extension carries the simplicial join bifunctor naturally to
the Day tensor bifunctor. -/
noncomputable def augDayJoinNatIso :
    Functor.uncurry.obj SSet.join.{u} ⋙ augDay.{u} ≅
      (augDay.{u}.prod augDay.{u}) ⋙ tensor DayCat.{u} :=
  NatIso.ofComponents (fun XY => augDayJoinIso XY.1 XY.2) (by
    rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
    change augDay.map ((SSet.join.map f).app Y ≫ (SSet.join.obj X').map g) ≫
        (augDayJoinIso X' Y').hom =
      (augDayJoinIso X Y).hom ≫ (augDay.map f ⊗ₘ augDay.map g)
    rw [Functor.map_comp, Category.assoc, augDayJoinIso_naturality_right g]
    rw [← Category.assoc, augDayJoinIso_naturality_left f, Category.assoc]
    rw [MonoidalCategory.tensorHom_def])

@[simp]
lemma augDayJoinNatIso_hom_app (X Y : SSet.{u}) :
    augDayJoinNatIso.{u}.hom.app (X, Y) = (augDayJoinIso X Y).hom :=
  rfl

end SSet.Join

namespace SSet

/-!
## Right-variable standard-simplex naturality and right inclusions
-/

namespace Join

/-- The augmented hom obtained by tensoring the identity with
`φ`, read in `SimplexCategory`, is `tensorHomOf (𝟙 _) φ`. -/
lemma down_id_tensorHom_ofHom (m : ℕ) {n n' : ℕ} (φ : ⦋n⦌ ⟶ ⦋n'⦌) :
    WithInitial.down (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ ofHom φ) =
      AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ :=
  rfl

/-- The Day-level computation behind naturality of
`joinStdSimplexIso` in the right variable (mirror of
`Join.augDay_map_whiskerRight_comp_joinStdSimplexIsoDay`). -/
lemma augDay_map_whiskerLeft_comp_joinStdSimplexIsoDay {m n n' : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) :
    (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
        Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n') ≪≫
          dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n'⦌)).hom) =
      ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
          (Join.augDayStdSimplexIso.{u} n) ≪≫
        dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom) ≫
        dayYonedaMap.{u}
          (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ ofHom φ) := by
  calc (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
          Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
              (Join.augDayStdSimplexIso.{u} n') ≪≫
            dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n'⦌)).hom)
      = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (Join.augDay.{u}.map (SSet.stdSimplex.map φ) ≫
            (Join.augDayStdSimplexIso.{u} n').hom)) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n'⦌)).hom := by
        rw [← MonoidalCategory.id_tensorHom, Iso.trans_hom,
          MonoidalCategory.tensorIso_hom, ← Category.assoc,
          MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
    _ = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          ((Join.augDayStdSimplexIso.{u} n).hom ≫
            dayYonedaMap.{u} (ofHom φ))) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n'⦌)).hom := by
        rw [augDayStdSimplexIso_naturality]
    _ = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (𝟙 (dayYoneda.{u} (WithInitial.of ⦋m⦌)) ⊗ₘ
            dayYonedaMap.{u} (ofHom φ)) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n'⦌)).hom := by
        rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
          Category.comp_id]
    _ = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom ≫
          dayYonedaMap.{u}
            (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ ofHom φ) := by
        rw [← dayYonedaMap_id (WithInitial.of ⦋m⦌),
          dayTensorYonedaIso_natural]
    _ = ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) ≫
          dayYonedaMap.{u}
            (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ ofHom φ) := by
        rw [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Category.assoc]

end Join

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `joinStdSimplexIso` in the right variable**:
joining a simplex-category map `φ` on the right and then applying
the join computation on standard simplices equals applying the
join computation first and then the ordinal-sum map
`tensorHomOf (𝟙 _) φ`. Mirror of
`SSet.joinStdSimplexIso_natural_left`. -/
@[reassoc]
theorem joinStdSimplexIso_natural_right {m n n' : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) :
    (join.{u}.obj (Δ[m] : SSet.{u})).map (SSet.stdSimplex.map φ) ≫
        (joinStdSimplexIso.{u} m n').hom =
      (joinStdSimplexIso.{u} m n).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) := by
  have hnat : Join.dropDay.{u}.map
        (Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
            Join.ofHom φ)) ≫
        (Join.dropYonedaIso ⦋m + n' + 1⦌).hom =
      (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) :=
    Join.dropYonedaIso_natural _
  have h1 : (joinStdSimplexIso.{u} m n').hom =
      Join.dropDay.{u}.map
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n') ≪≫
          Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n'⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := rfl
  have h2 : (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := rfl
  have key : (join.{u}.obj (Δ[m] : SSet.{u})).map (SSet.stdSimplex.map φ) ≫
        (joinStdSimplexIso.{u} m n').hom =
      (Join.dropDay.{u}.map
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
              (Join.augDayStdSimplexIso.{u} n) ≪≫
            Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        Join.dropDay.{u}.map
          (Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
            Join.ofHom φ))) ≫
        (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := by
    have step1 : (join.{u}.obj (Δ[m] : SSet.{u})).map
            (SSet.stdSimplex.map φ) ≫
            (joinStdSimplexIso.{u} m n').hom =
          (Join.dropDay.{u}.map
              (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
            Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m)
                  (Join.augDayStdSimplexIso.{u} n') ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                  (WithInitial.of ⦋n'⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := by
      rw [h1, join_obj_map_eq]
      simp only [Category.assoc]
    have step2 : (Join.dropDay.{u}.map
              (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
            Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m)
                  (Join.augDayStdSimplexIso.{u} n') ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                  (WithInitial.of ⦋n'⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom =
          Join.dropDay.{u}.map
              ((Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                  Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
                ((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n') ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n'⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := by
      rw [← Join.dropDay.map_comp]
    have step3 : Join.dropDay.{u}.map
              ((Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                  Join.augDay.{u}.map (SSet.stdSimplex.map φ)) ≫
                ((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n') ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n'⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom =
          Join.dropDay.{u}.map
              (((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n⦌)).hom) ≫
                Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
                  Join.ofHom φ)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := by
      rw [Join.augDay_map_whiskerLeft_comp_joinStdSimplexIsoDay]
    have step4 : Join.dropDay.{u}.map
              (((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n⦌)).hom) ≫
                Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
                  Join.ofHom φ)) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom =
          (Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m)
                  (Join.augDayStdSimplexIso.{u} n) ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                  (WithInitial.of ⦋n⦌)).hom) ≫
            Join.dropDay.{u}.map
              (Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
                Join.ofHom φ))) ≫
            (Join.dropYonedaIso ⦋m + n' + 1⦌).hom := by
      rw [Join.dropDay.map_comp]
    exact step1.trans (step2.trans (step3.trans step4))
  have step5 : (Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          Join.dropDay.{u}.map
            (Join.dayYonedaMap.{u} (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
              Join.ofHom φ))) ≫
          (Join.dropYonedaIso ⦋m + n' + 1⦌).hom =
        Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
            SSet.stdSimplex.map
              (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) := by
    simp only [Category.assoc]
    rw [hnat]
  have step6 : Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
            SSet.stdSimplex.map
              (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) =
        (joinStdSimplexIso.{u} m n).hom ≫
          SSet.stdSimplex.map
            (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) := by
    conv_rhs => rw [h2]
    simp only [Category.assoc]
  exact key.trans (step5.trans step6)

namespace Join

/-- The left unitor at `op (of ⦋n⦌)` in the opposite augmented
simplex category is the identity (mirror of
`Join.rightUnitor_op_of_inv`). -/
lemma leftUnitor_op_of_inv (n : ℕ) :
    (λ_ (op (WithInitial.of ⦋n⦌) : AugmentedSimplexCategoryᵒᵖ)).inv =
      𝟙 (op (WithInitial.of ⦋n⦌)) :=
  rfl

/-- In the augmented simplex category, `inr` at `of`-objects is
tensoring with the identity on the right (mirror of
`Join.inl_of_eq`). -/
lemma inr_of_eq (m n : ℕ) :
    AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
        (WithInitial.of ⦋n⦌) =
      WithInitial.starInitial.to (WithInitial.of ⦋m⦌) ⊗ₘ
        𝟙 (WithInitial.of ⦋n⦌) := by
  have hlam : (λ_ (WithInitial.of ⦋n⦌)) = Iso.refl (WithInitial.of ⦋n⦌) :=
    rfl
  rw [AugmentedSimplexCategory.inr, hlam]
  simp only [Iso.refl_inv, MonoidalCategory.tensorHom_id]
  exact Category.id_comp _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The left-unitor element computation**: the inverse left
unitor in `DayCat` sends an element `e` at `op (of ⦋n⦌)` to the
`η`-element `(ν, e)`. Mirror of `Join.rightUnitor_inv_app_of`. -/
lemma leftUnitor_inv_app_of (n : ℕ) :
    (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv.natTrans.app
        (op (WithInitial.of ⦋n⦌)) (ULift.up (𝟙 ⦋n⦌)) =
      (DayFunctor.η (𝟙_ DayCat.{u}) (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
        (op WithInitial.star, op (WithInitial.of ⦋n⦌))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit,
          ULift.up (𝟙 ⦋n⦌)) := by
  have hstruct :=
    LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
      (Type u) (augDay.{u}.obj (Δ[n] : SSet.{u}))
      (op (WithInitial.of ⦋n⦌))
  have hstruct' : (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) ▷
          (augDay.{u}.obj (Δ[n] : SSet.{u})).functor.obj
            (op (WithInitial.of ⦋n⦌))) ≫
        (DayFunctor.η (𝟙_ DayCat.{u})
          (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌)) ≫
        (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).hom.natTrans.app
          (op (WithInitial.of ⦋n⦌)) =
      (λ_ ((augDay.{u}.obj (Δ[n] : SSet.{u})).functor.obj
          (op (WithInitial.of ⦋n⦌)))).hom ≫
        (augDay.{u}.obj (Δ[n] : SSet.{u})).functor.map
          (λ_ (op (WithInitial.of ⦋n⦌))).inv :=
    hstruct
  have h2 := types_congr_hom hstruct'
    ((PUnit.unit : (PUnit : Type u)), ULift.up (𝟙 ⦋n⦌))
  simp only [comp_apply] at h2
  have h2' : (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).hom.natTrans.app
        (op (WithInitial.of ⦋n⦌))
        ((DayFunctor.η (𝟙_ DayCat.{u})
            (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌))
          (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
              PUnit.unit,
            ULift.up (𝟙 ⦋n⦌))) =
      ULift.up (𝟙 ⦋n⦌) := by
    have hmapid : (augDay.{u}.obj (Δ[n] : SSet.{u})).functor.map
          (λ_ (op (WithInitial.of ⦋n⦌))).inv (ULift.up (𝟙 ⦋n⦌)) =
        ULift.up (𝟙 ⦋n⦌) := by
      rw [leftUnitor_op_of_inv]
      simp only [CategoryTheory.Functor.map_id]
      rfl
    exact h2.trans hmapid
  have hcomp : (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv.natTrans.app
        (op (WithInitial.of ⦋n⦌))
        ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).hom.natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (𝟙_ DayCat.{u})
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
                PUnit.unit,
              ULift.up (𝟙 ⦋n⦌)))) =
      (DayFunctor.η (𝟙_ DayCat.{u})
          (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
        (op WithInitial.star, op (WithInitial.of ⦋n⦌))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
            PUnit.unit,
          ULift.up (𝟙 ⦋n⦌)) := by
    have hid : ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).hom ≫
          (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv).natTrans =
        𝟙 _ := by
      have hcong := congrArg DayFunctor.Hom.natTrans
        (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).hom_inv_id
      rwa [dayIdNatTrans] at hcong
    have happ := types_congr_hom
      (NatTrans.congr_app hid (op (WithInitial.of ⦋n⦌)))
      ((DayFunctor.η (𝟙_ DayCat.{u})
          (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
        (op WithInitial.star, op (WithInitial.of ⦋n⦌))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit,
          ULift.up (𝟙 ⦋n⦌)))
    simp only [NatTrans.id_app, types_id_apply] at happ
    exact happ
  rw [h2'] at hcomp
  exact hcomp

end Join

namespace Join

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The Yoneda-element chase for `joinInr`**: the composite in
`DayCat` obtained by expanding `joinInr Δ[m] Δ[n]` (left unitor,
then whiskering the unique map out of the empty simplicial set
on the left) and `joinStdSimplexIso m n` equals
`augDayStdSimplexIso` followed by the representable map of
`inr`. Mirror of `SSet.Join.joinInlDay_eq`: the
proof evaluates both sides, after precomposing with
`(augDayStdSimplexIso n).inv`, on the universal element
`ULift.up (𝟙 (of ⦋n⦌))`: `SSet.Join.leftUnitor_inv_app_of`
 writes it as an `η`-element, the whisker steps
push it through the tensor, the degree `-1` components compute
by the defining component lemmas, and `η_comp_tensorDesc_app`
finishes at `ULift.up (starInitial.to ⊗ₘ 𝟙) = ULift.up (inr ..)`
(`SSet.Join.inr_of_eq`). -/
lemma joinInrDay_eq (m n : ℕ) :
    (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
        (dayUnitYonedaIso.{u}.hom ▷ augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        (augDayBotIso.{u}.inv ▷ augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
          augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (augDayStdSimplexIso.{u} n).hom) ≫
        (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom =
      (augDayStdSimplexIso.{u} n).hom ≫
        dayYonedaMap.{u}
          (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)) := by
  have key : (augDayStdSimplexIso.{u} n).inv ≫
        ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
          (dayUnitYonedaIso.{u}.hom ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (augDayBotIso.{u}.inv ▷ augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) =
      dayYonedaMap.{u}
        (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)) := by
    have s3 : (dayUnitYonedaIso.{u}.hom ▷
          augDay.{u}.obj (Δ[n] : SSet.{u})).natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (𝟙_ DayCat.{u})
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
                PUnit.unit,
              ULift.up (𝟙 ⦋n⦌))) =
        (DayFunctor.η (dayYoneda.{u} WithInitial.star)
            (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌))
          (ULift.up (𝟙 WithInitial.star), ULift.up (𝟙 ⦋n⦌)) := by
      have h := types_congr_hom
        (η_whiskerRight_app (𝟙_ DayCat.{u})
          (dayYoneda.{u} WithInitial.star)
          (augDay.{u}.obj (Δ[n] : SSet.{u}))
          dayUnitYonedaIso.{u}.hom (op WithInitial.star)
          (op (WithInitial.of ⦋n⦌)))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit,
          ULift.up (𝟙 ⦋n⦌))
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s4 : (augDayBotIso.{u}.inv ▷
          augDay.{u}.obj (Δ[n] : SSet.{u})).natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (dayYoneda.{u} WithInitial.star)
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (ULift.up (𝟙 WithInitial.star), ULift.up (𝟙 ⦋n⦌))) =
        (DayFunctor.η (augDay.{u}.obj (⊥_ SSet.{u}))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌))
          (PUnit.unit, ULift.up (𝟙 ⦋n⦌)) := by
      have h := types_congr_hom
        (η_whiskerRight_app (dayYoneda.{u} WithInitial.star)
          (augDay.{u}.obj (⊥_ SSet.{u}))
          (augDay.{u}.obj (Δ[n] : SSet.{u}))
          augDayBotIso.{u}.inv (op WithInitial.star)
          (op (WithInitial.of ⦋n⦌)))
        (ULift.up (𝟙 WithInitial.star), ULift.up (𝟙 ⦋n⦌))
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s5 : (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
          augDay.{u}.obj (Δ[n] : SSet.{u})).natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (augDay.{u}.obj (⊥_ SSet.{u}))
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (PUnit.unit, ULift.up (𝟙 ⦋n⦌))) =
        (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌))
          (PUnit.unit, ULift.up (𝟙 ⦋n⦌)) := by
      have h := types_congr_hom
        (η_whiskerRight_app (augDay.{u}.obj (⊥_ SSet.{u}))
          (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (augDay.{u}.obj (Δ[n] : SSet.{u}))
          (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})))
          (op WithInitial.star) (op (WithInitial.of ⦋n⦌)))
        (PUnit.unit, ULift.up (𝟙 ⦋n⦌))
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s6 : ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (augDayStdSimplexIso.{u} n).hom).natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (PUnit.unit, ULift.up (𝟙 ⦋n⦌))) =
        (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
          (op WithInitial.star, op (WithInitial.of ⦋n⦌))
          (ULift.up
              (WithInitial.starInitial.to (WithInitial.of ⦋m⦌)),
            ULift.up (𝟙 (WithInitial.of ⦋n⦌))) := by
      have ht : ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) =
          ((augDayStdSimplexIso.{u} m).hom ▷
              augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (dayYoneda.{u} (WithInitial.of ⦋m⦌) ◁
              (augDayStdSimplexIso.{u} n).hom) :=
        MonoidalCategory.tensorHom_def _ _
      have hs1 : ((augDayStdSimplexIso.{u} m).hom ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})).natTrans.app
            (op (WithInitial.of ⦋n⦌))
            ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
                (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
              (op WithInitial.star, op (WithInitial.of ⦋n⦌))
              (PUnit.unit, ULift.up (𝟙 ⦋n⦌))) =
          (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (ULift.up
                (WithInitial.starInitial.to
                  (WithInitial.of ⦋m⦌)),
              ULift.up (𝟙 ⦋n⦌)) := by
        have h := types_congr_hom
          (η_whiskerRight_app (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))
            (augDayStdSimplexIso.{u} m).hom
            (op WithInitial.star) (op (WithInitial.of ⦋n⦌)))
          (PUnit.unit, ULift.up (𝟙 ⦋n⦌))
        simp only [comp_apply] at h
        refine h.trans ?_
        congr 1
      have hs2 : (dayYoneda.{u} (WithInitial.of ⦋m⦌) ◁
            (augDayStdSimplexIso.{u} n).hom).natTrans.app
            (op (WithInitial.of ⦋n⦌))
            ((DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
                (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
              (op WithInitial.star, op (WithInitial.of ⦋n⦌))
              (ULift.up
                  (WithInitial.starInitial.to
                    (WithInitial.of ⦋m⦌)),
                ULift.up (𝟙 ⦋n⦌))) =
          (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (ULift.up
                (WithInitial.starInitial.to
                  (WithInitial.of ⦋m⦌)),
              ULift.up (𝟙 (WithInitial.of ⦋n⦌))) := by
        have h := types_congr_hom
          (η_whiskerLeft_app (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))
            (dayYoneda.{u} (WithInitial.of ⦋n⦌))
            (augDayStdSimplexIso.{u} n).hom
            (op WithInitial.star) (op (WithInitial.of ⦋n⦌)))
          (ULift.up
              (WithInitial.starInitial.to (WithInitial.of ⦋m⦌)),
            ULift.up (𝟙 ⦋n⦌))
        simp only [comp_apply] at h
        refine h.trans ?_
        congr 1
      rw [ht]
      simp only [dayCompNatTrans, NatTrans.comp_app, comp_apply]
      rw [hs1, hs2]
    have s7 : (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom.natTrans.app
          (op (WithInitial.of ⦋n⦌))
          ((DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
            (op WithInitial.star, op (WithInitial.of ⦋n⦌))
            (ULift.up
                (WithInitial.starInitial.to
                  (WithInitial.of ⦋m⦌)),
              ULift.up (𝟙 (WithInitial.of ⦋n⦌)))) =
        ULift.up (WithInitial.starInitial.to
            (WithInitial.of ⦋m⦌) ⊗ₘ
          𝟙 (WithInitial.of ⦋n⦌)) := by
      have h := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (yonedaTensorNatTrans.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌))
          (op WithInitial.star) (op (WithInitial.of ⦋n⦌)))
        (ULift.up
            (WithInitial.starInitial.to (WithInitial.of ⦋m⦌)),
          ULift.up (𝟙 (WithInitial.of ⦋n⦌)))
      simp only [comp_apply] at h
      exact h
    apply DayFunctor.hom_ext
    apply uliftYonedaEquiv.injective
    rw [show uliftYonedaEquiv
          ((augDayStdSimplexIso.{u} n).inv ≫
            ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
              (dayUnitYonedaIso.{u}.hom ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              (augDayBotIso.{u}.inv ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
                (augDayStdSimplexIso.{u} n).hom) ≫
              (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom)).natTrans =
        ((augDayStdSimplexIso.{u} n).inv ≫
          ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
            (dayUnitYonedaIso.{u}.hom ▷
              augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (augDayBotIso.{u}.inv ▷
              augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
              augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (augDayStdSimplexIso.{u} n).hom) ≫
            (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom)).natTrans.app
          (op (WithInitial.of ⦋n⦌))
          (ULift.up (𝟙 (WithInitial.of ⦋n⦌))) from rfl,
      show uliftYonedaEquiv
          (dayYonedaMap.{u}
            (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌))).natTrans =
        ULift.up (𝟙 (WithInitial.of ⦋n⦌) ≫
          AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)) from rfl]
    simp only [dayCompNatTrans, NatTrans.comp_app, comp_apply]
    rw [augDayStdSimplexIso_inv_app_of, leftUnitor_inv_app_of, s3, s4,
      s5, s6, s7, Category.id_comp, inr_of_eq]
  calc (λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
          (dayUnitYonedaIso.{u}.hom ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (augDayBotIso.{u}.inv ▷ augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom
      = (augDayStdSimplexIso.{u} n).hom ≫
          ((augDayStdSimplexIso.{u} n).inv ≫
            ((λ_ (augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
              (dayUnitYonedaIso.{u}.hom ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              (augDayBotIso.{u}.inv ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              (augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
                augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
              ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
                (augDayStdSimplexIso.{u} n).hom) ≫
              (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom)) := by
        conv_rhs => rw [← Category.assoc,
          (augDayStdSimplexIso.{u} n).hom_inv_id, Category.id_comp]
    _ = (augDayStdSimplexIso.{u} n).hom ≫
          dayYonedaMap.{u}
            (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)) := by
        rw [key]

end Join

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **`joinInr` on standard simplices is `inr'`**: the right
endpoint inclusion of a join of standard simplices, transported
along `joinStdSimplexIso`, is the standard-simplex map of
`AugmentedSimplexCategory.inr'`. Mirror of
`SSet.joinInl_comp_joinStdSimplexIso_hom`; expanding `joinInr`
(left unitor, then whiskering `initial.to` on the left) and
`joinStdSimplexIso` in `DayCat` reduces it to
`SSet.Join.joinInrDay_eq` and naturality of `dropYonedaIso`. -/
theorem joinInr_comp_joinStdSimplexIso_hom (m n : ℕ) :
    joinInr (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m n).hom =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) := by
  have hInr : joinInr (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) =
      Join.dropDay.{u}.map
        ((λ_ (Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
          (Join.dayUnitYonedaIso.{u}.hom ▷
            Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (Join.augDayBotIso.{u}.inv ▷
            Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          (Join.augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
            Join.augDay.{u}.obj (Δ[n] : SSet.{u}))) := by
    simp only [joinInr, botJoinIso, join_map_app_eq, Functor.mapIso_inv,
      Iso.trans_inv, MonoidalCategory.tensorIso_inv, Iso.refl_inv,
      Iso.symm_inv, MonoidalCategory.tensorHom_id,
      ← Join.dropDay.map_comp, Category.assoc]
  have hIso : (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
          (((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    have hrfl : (joinStdSimplexIso.{u} m n).hom =
        Join.dropDay.{u}.map
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
              (Join.augDayStdSimplexIso.{u} n) ≪≫
            Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom := rfl
    rw [hrfl, Iso.trans_hom, MonoidalCategory.tensorIso_hom]
  have step1 : joinInr (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
          ((λ_ (Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
            (Join.dayUnitYonedaIso.{u}.hom ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (Join.augDayBotIso.{u}.inv ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (Join.augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    rw [hInr, hIso]
    simp only [← Category.assoc, ← Join.dropDay.map_comp]
  have step2 : Join.dropDay.{u}.map
          ((λ_ (Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
            (Join.dayUnitYonedaIso.{u}.hom ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (Join.augDayBotIso.{u}.inv ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (Join.augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
              Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom =
      Join.dropDay.{u}.map
          ((Join.augDayStdSimplexIso.{u} n).hom ≫
            Join.dayYonedaMap.{u}
              (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌))) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    rw [Join.joinInrDay_eq]
  have step3 : Join.dropDay.{u}.map
          ((Join.augDayStdSimplexIso.{u} n).hom ≫
            Join.dayYonedaMap.{u}
              (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌))) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) := by
    rw [Join.dropDay.map_comp]
    simp only [Category.assoc]
    rw [Join.dropYonedaIso_natural,
      ← Category.assoc (Join.dropDay.{u}.map
        (Join.augDayStdSimplexIso.{u} n).hom),
      Join.dropDay_map_augDayStdSimplexIso_hom_comp_dropYonedaIso]
    exact Category.id_comp _
  exact step1.trans (step2.trans step3)


/-- The conjugation form of naturality of `joinStdSimplexIso` in
the right variable: precomposition with its inverse commutes with
joins of simplex-category maps on the right. -/
theorem joinStdSimplexIso_inv_comp_join_obj_map {n n' : ℕ}
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (m : ℕ) :
    (joinStdSimplexIso.{u} m n).inv ≫
        (join.{u}.obj (Δ[m] : SSet.{u})).map (SSet.stdSimplex.map φ) =
      SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) ≫
        (joinStdSimplexIso.{u} m n').inv := by
  have h := joinStdSimplexIso_natural_right (m := m) φ
  rw [Iso.inv_comp_eq, ← Category.assoc (joinStdSimplexIso.{u} m n).hom,
    ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SSet
