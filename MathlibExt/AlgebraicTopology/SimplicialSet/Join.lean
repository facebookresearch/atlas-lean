/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# The join of simplicial sets

The join `X ⋆ Y` is constructed by Day convolution on augmented simplicial
sets. The augmented simplex category `AugmentedSimplexCategory` carries the
ordinal-sum monoidal structure with `⦋m⦌ ⊗ ⦋n⦌ = ⦋m + n + 1⦌` and tensor
unit the initial object `star` (degree `-1`). A simplicial set `X` is
extended to an augmented simplicial set by putting a one-point set in
degree `-1` (`SSet.Join.aug`); the join is the restriction
(`SSet.Join.dropDay`) of the Day convolution tensor product of the two
extensions.

The main declarations are:
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor ExternalProduct
  CategoryTheory.Prod

universe u

namespace SSet

namespace Join

/-- Augmented simplicial sets: presheaves on the augmented simplex category,
viewed as Day functors for the ordinal-sum monoidal structure. -/
abbrev DayCat : Type (u + 1) := AugmentedSimplexCategoryᵒᵖ ⊛⥤ Type u

/-- The functor sending a simplicial set to the augmented simplicial object
with terminal point (the constant augmentation). -/
def augmentTerminal : SSet.{u} ⥤ SimplicialObject.Augmented (Type u) where
  obj X := SimplicialObject.augmentOfIsTerminal X Types.isTerminalPUnit
  map f :=
    { left := f
      right := Types.isTerminalPUnit.from _
      w := by
        apply NatTrans.ext
        funext n
        apply Types.isTerminalPUnit.hom_ext }
  map_id _ := by
    apply SimplicialObject.Augmented.hom_ext
    · rfl
    · apply Types.isTerminalPUnit.hom_ext
  map_comp _ _ := by
    apply SimplicialObject.Augmented.hom_ext
    · rfl
    · apply Types.isTerminalPUnit.hom_ext

/-- Extend a simplicial set to an augmented simplicial set (a presheaf on the
augmented simplex category) by putting a one-point set in degree `-1`. -/
def aug : SSet.{u} ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  augmentTerminal ⋙
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse

/-- Restrict an augmented simplicial set to a simplicial set. -/
def drop : (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj AugmentedSimplexCategory.inclusion.op

lemma aug_obj_obj_of (X : SSet.{u}) (n : SimplexCategory) :
    (aug.obj X).obj (op (WithInitial.of n)) = X.obj (op n) := rfl

lemma aug_obj_obj_star (X : SSet.{u}) :
    (aug.obj X).obj (op WithInitial.star) = (PUnit : Type u) := rfl

lemma drop_obj_aug_obj (X : SSet.{u}) : drop.obj (aug.obj X) = X := rfl

/-- The augmented extension, regarded as landing in the Day-convolution
category of augmented simplicial sets. -/
def augDay : SSet.{u} ⥤ DayCat.{u} :=
  aug ⋙ (MonoidalCategory.DayFunctor.equiv _ _).inverse

/-- Drop the augmentation, from Day functors to simplicial sets. -/
def dropDay : DayCat.{u} ⥤ SSet.{u} :=
  (MonoidalCategory.DayFunctor.equiv _ _).functor ⋙ drop

lemma augDay_obj_functor (X : SSet.{u}) :
    (augDay.obj X).functor = aug.obj X := rfl

lemma dropDay_obj (F : DayCat.{u}) : dropDay.obj F = drop.obj F.functor := rfl

/-- Any two elements of `ULift (star ⟶ a)` agree, since `star` is initial. -/
lemma ulift_hom_star_eq {a : AugmentedSimplexCategory}
    (x y : ULift.{u} (WithInitial.star ⟶ a)) : x = y :=
  ULift.ext (WithInitial.starInitial.hom_ext _ _)

/-- The one-point type, identified with `ULift` of maps out of `star`. -/
def punitIsoULiftHomStar (a : AugmentedSimplexCategory) :
    (PUnit : Type u) ≅ ULift.{u} (WithInitial.star ⟶ a) :=
  Equiv.toIso
    { toFun _ := ⟨WithInitial.starInitial.to a⟩
      invFun _ := PUnit.unit
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := ulift_hom_star_eq _ _ }

/-- `ULift` of maps into `star` is initial in `Type u`, since there are none. -/
def isInitialULiftHomToStar (a : SimplexCategory) :
    IsInitial (ULift.{u} (WithInitial.of a ⟶ WithInitial.star) : Type u) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ ↾fun (x : ULift.{u} (WithInitial.of a ⟶ WithInitial.star)) ↦
      (WithInitial.false_of_to_star x.down).elim)
    (fun _ _ ↦ by ext ⟨x⟩; exact (WithInitial.false_of_to_star x).elim)

/-- The sets of simplices of the empty simplicial set are initial types. -/
def isInitialBotObj (x : SimplexCategoryᵒᵖ) :
    IsInitial ((⊥_ SSet.{u}).obj x) :=
  initialIsInitial.isInitialObj ((CategoryTheory.evaluation _ _).obj x)

/-- The augmented extension of a standard simplex is the augmented
representable presheaf on the corresponding object. -/
def augStdSimplexIso (n : SimplexCategory) :
    aug.{u}.obj (stdSimplex.obj n) ≅ uliftYoneda.{u}.obj (WithInitial.of n) :=
  NatIso.ofComponents
    (fun x ↦ WithInitial.rec
      (motive := fun (a : AugmentedSimplexCategory) ↦
        (aug.obj (stdSimplex.obj n)).obj (op a) ≅
          (uliftYoneda.obj (WithInitial.of n)).obj (op a))
      (fun _ ↦ Iso.refl _)
      (punitIsoULiftHomStar _)
      x.unop)
    (by
      intro x y f
      obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = op b := ⟨y.unop, rfl⟩
      cases a with
      | of m =>
        cases b with
        | of k =>
          ext e
          obtain ⟨g⟩ := e
          rfl
        | star =>
          ext e
          apply ulift_hom_star_eq
      | star =>
        cases b with
        | of k => exact (WithInitial.false_of_to_star f.unop).elim
        | star =>
          ext e
          apply ulift_hom_star_eq)

/-- The augmented extension of the empty simplicial set is the augmented
representable presheaf on `star`, the tensor unit. -/
def augBotIso :
    aug.obj (⊥_ SSet.{u}) ≅ uliftYoneda.obj WithInitial.star :=
  NatIso.ofComponents
    (fun x ↦ WithInitial.rec
      (motive := fun (a : AugmentedSimplexCategory) ↦
        (aug.obj (⊥_ SSet.{u})).obj (op a) ≅
          (uliftYoneda.obj WithInitial.star).obj (op a))
      (fun k ↦ (isInitialBotObj (op k)).uniqueUpToIso (isInitialULiftHomToStar k))
      (punitIsoULiftHomStar _)
      x.unop)
    (by
      intro x y f
      obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = op b := ⟨y.unop, rfl⟩
      cases a with
      | of m =>
        exact (isInitialBotObj (op m)).hom_ext _ _
      | star =>
        cases b with
        | of k => exact (WithInitial.false_of_to_star f.unop).elim
        | star =>
          ext e
          apply ulift_hom_star_eq)

/-- Tensoring morphisms gives the unit transformation exhibiting the
representable at `a ⊗ b` as a Day convolution of representables. -/
def yonedaTensorNatTrans (a b : AugmentedSimplexCategory) :
    (uliftYoneda.{u}.obj a) ⊠ (uliftYoneda.{u}.obj b) ⟶
      tensor AugmentedSimplexCategoryᵒᵖ ⋙ uliftYoneda.{u}.obj (a ⊗ b) where
  app _ := ↾fun q ↦ ULift.up (q.1.down ⊗ₘ q.2.down)
  naturality _ _ φ := by
    apply TypeCat.homEquiv.injective
    funext ⟨⟨f⟩, ⟨g⟩⟩
    simp only [Functor.comp_obj, tensor_obj,
      externalProductBifunctor_obj_obj, externalProductBifunctor_obj_map,
      uliftYoneda_obj_map, yoneda_obj_obj, unop_tensorObj, Category.assoc,
      TypeCat.homEquiv_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Functor.comp_map, tensor_map, unop_tensorHom,
      tensorHom_comp_tensorHom]
    rw [CategoryTheory.whiskerLeft_apply, CategoryTheory.whiskerRight_apply]
    rfl

/-- The augmented representable, as a Day functor. -/
abbrev dayYoneda (a : AugmentedSimplexCategory) : DayCat.{u} :=
  DayFunctor.mk (uliftYoneda.{u}.obj a)

/-- The Day tensor of two augmented representables is the representable
on the tensor product (ordinal sum) of the representing objects. -/
def dayTensorYonedaIso (a b : AugmentedSimplexCategory) :
    dayYoneda.{u} a ⊗ dayYoneda.{u} b ≅ dayYoneda.{u} (a ⊗ b) where
  hom := DayFunctor.tensorDesc (yonedaTensorNatTrans.{u} a b)
  inv := ⟨uliftYonedaEquiv.symm
    ((DayFunctor.η (dayYoneda.{u} a) (dayYoneda.{u} b)).app (op a, op b)
      (ULift.up (𝟙 a), ULift.up (𝟙 b)))⟩
  hom_inv_id := by
    apply DayFunctor.tensor_hom_ext
    intro x y
    apply TypeCat.homEquiv.injective
    funext ⟨⟨f⟩, ⟨g⟩⟩
    have hnat := types_congr_hom
      (NatTrans.naturality (DayFunctor.η (dayYoneda.{u} a) (dayYoneda.{u} b))
        (f.op ×ₘ g.op))
      (ULift.up (𝟙 a), ULift.up (𝟙 b))
    have hmap : ((dayYoneda.{u} a).functor ⊠ (dayYoneda.{u} b).functor).map (f.op ×ₘ g.op)
        (ULift.up (𝟙 a), ULift.up (𝟙 b)) = (ULift.up f, ULift.up g) := by
      simp only [op_unop, externalProductBifunctor_obj_obj,
        externalProductBifunctor_obj_map, uliftYoneda_obj_map,
        Quiver.Hom.unop_op, comp_apply, yoneda_obj_obj]
      rw [CategoryTheory.whiskerLeft_apply, CategoryTheory.whiskerRight_apply]
      simp
    have hα : (yonedaTensorNatTrans.{u} a b).app (x, y) (ULift.up f, ULift.up g)
        = ULift.up (f ⊗ₘ g) := rfl
    simp only [CategoryTheory.comp_apply, Functor.comp_map, tensor_map] at hnat
    rw [hmap] at hnat
    simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
      op_tensorObj, yoneda_obj_obj, DayFunctor.comp_natTrans,
      NatTrans.comp_app, DayFunctor.η_comp_tensorDesc_app_assoc,
      TypeCat.homEquiv_apply, comp_apply, DayFunctor.id_natTrans,
      NatTrans.id_app, Category.comp_id]
    rw [hα]
    exact hnat.symm
  inv_hom_id := by
    apply DayFunctor.hom_ext
    apply uliftYonedaEquiv.injective
    have key := types_congr_hom
      (DayFunctor.η_comp_tensorDesc_app (yonedaTensorNatTrans.{u} a b) (op a) (op b))
      (ULift.up (𝟙 a), ULift.up (𝟙 b))
    have hα : (yonedaTensorNatTrans.{u} a b).app (op a, op b)
        (ULift.up (𝟙 a), ULift.up (𝟙 b)) = ULift.up (𝟙 (a ⊗ b)) := by
      simp [yonedaTensorNatTrans]
    simp only [CategoryTheory.comp_apply] at key
    rw [hα] at key
    change uliftYonedaEquiv.{u}
      (uliftYonedaEquiv.{u}.symm _ ≫
        (DayFunctor.tensorDesc (yonedaTensorNatTrans.{u} a b)).natTrans) = _
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact key

lemma dayCompNatTrans {F G H : DayCat.{u}} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).natTrans = α.natTrans ≫ β.natTrans := rfl

lemma dayIdNatTrans (F : DayCat.{u}) :
    DayFunctor.Hom.natTrans (CategoryStruct.id F) = 𝟙 F.functor := rfl

/-- The Day-convolution unit is the augmented representable on `star`. -/
def dayUnitYonedaIso : (𝟙_ DayCat.{u}) ≅ dayYoneda WithInitial.star where
  hom := DayFunctor.unitDesc (↾fun _ ↦ ULift.up (𝟙 WithInitial.star))
  inv := ⟨uliftYonedaEquiv.symm
    (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)⟩
  hom_inv_id := by
    apply DayFunctor.unit_hom_ext
    apply TypeCat.homEquiv.injective
    funext pt
    obtain ⟨⟩ := pt
    have key := types_congr_hom
      (DayFunctor.ν_comp_unitDesc
        (F := dayYoneda.{u} WithInitial.star)
        (↾fun _ ↦ ULift.up (𝟙 WithInitial.star))) PUnit.unit
    simp only [CategoryTheory.comp_apply] at key
    simp only [key, yoneda_obj_obj, unop_tensorUnit,
      DayFunctor.comp_natTrans, NatTrans.comp_app,
      uliftYonedaEquiv_symm_apply_app, TypeCat.homEquiv_apply,
      comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      DayFunctor.id_natTrans, NatTrans.id_app, Category.comp_id]
    have hop : (𝟙 (WithInitial.star : AugmentedSimplexCategory)).op
        = 𝟙 (op (WithInitial.star : AugmentedSimplexCategory)) :=
      CategoryTheory.op_id
    rw [hop]
    simp
  inv_hom_id := by
    apply DayFunctor.hom_ext
    apply uliftYonedaEquiv.injective
    have key := types_congr_hom
      (DayFunctor.ν_comp_unitDesc
        (F := dayYoneda.{u} WithInitial.star)
        (↾fun _ ↦ ULift.up (𝟙 WithInitial.star))) PUnit.unit
    simp only [CategoryTheory.comp_apply] at key
    rw [dayCompNatTrans, dayIdNatTrans, uliftYonedaEquiv_comp,
      Equiv.apply_symm_apply]
    exact key

/-- Dropping the augmentation of an augmented representable on `of k`
gives the standard simplex `Δ[k]`. -/
def dropYonedaIso (k : SimplexCategory) :
    drop.obj (uliftYoneda.{u}.obj (WithInitial.of k)) ≅ stdSimplex.obj k :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by
      intro x y f
      ext e
      obtain ⟨g⟩ := e
      rfl)

/-- The augmented extension of `Δ[k]`, as a Day functor, is representable. -/
def augDayStdSimplexIso (k : ℕ) :
    augDay.{u}.obj Δ[k] ≅ dayYoneda.{u} (WithInitial.of ⦋k⦌) :=
  (DayFunctor.equiv _ _).inverse.mapIso (augStdSimplexIso ⦋k⦌)

/-- The augmented extension of the empty simplicial set, as a Day functor,
is representable on `star`. -/
def augDayBotIso :
    augDay.obj (⊥_ SSet.{u}) ≅ dayYoneda WithInitial.star :=
  (DayFunctor.equiv _ _).inverse.mapIso augBotIso

end Join

/-- The join bifunctor on simplicial sets: extend both factors to augmented
simplicial sets, take their Day convolution for the ordinal-sum monoidal
structure on the augmented simplex category, and drop the augmentation. -/
def join : SSet.{u} ⥤ SSet.{u} ⥤ SSet.{u} :=
  Functor.curryObj
    ((Join.augDay.prod Join.augDay) ⋙ tensor Join.DayCat.{u} ⋙ Join.dropDay)

/-- The join of two simplicial sets. -/
abbrev joinObj (X Y : SSet.{u}) : SSet.{u} := (join.obj X).obj Y

/-- Notation for the join of simplicial sets. -/
scoped[Simplicial] infixr:70 " ⋆ " => SSet.joinObj

lemma joinObj_eq (X Y : SSet.{u}) :
    X ⋆ Y = Join.dropDay.obj (Join.augDay.obj X ⊗ Join.augDay.obj Y) := rfl

/-- The join of two standard simplices is a standard simplex:
`Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]`. -/
def joinStdSimplexIso (m n : ℕ) :
    (Δ[m] : SSet.{u}) ⋆ Δ[n] ≅ Δ[m + n + 1] :=
  Join.dropDay.mapIso
      (MonoidalCategory.tensorIso (Join.augDayStdSimplexIso m)
        (Join.augDayStdSimplexIso n) ≪≫
        Join.dayTensorYonedaIso (WithInitial.of ⦋m⦌) (WithInitial.of ⦋n⦌)) ≪≫
    Join.dropYonedaIso ⦋m + n + 1⦌

/-- The empty simplicial set is a left unit for the join. -/
def botJoinIso (X : SSet.{u}) : (⊥_ SSet.{u}) ⋆ X ≅ X :=
  Join.dropDay.mapIso
    (MonoidalCategory.tensorIso Join.augDayBotIso
        (Iso.refl (Join.augDay.obj X)) ≪≫
      MonoidalCategory.tensorIso Join.dayUnitYonedaIso.symm
        (Iso.refl (Join.augDay.obj X)) ≪≫
      λ_ (Join.augDay.obj X))

/-- The empty simplicial set is a right unit for the join. -/
def joinBotIso (X : SSet.{u}) : X ⋆ (⊥_ SSet.{u}) ≅ X :=
  Join.dropDay.mapIso
    (MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X))
        Join.augDayBotIso ≪≫
      MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X))
        Join.dayUnitYonedaIso.symm ≪≫
      ρ_ (Join.augDay.obj X))

end SSet

end
