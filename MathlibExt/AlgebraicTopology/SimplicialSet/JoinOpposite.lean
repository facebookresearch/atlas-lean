/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinProperties
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Reversal of the original simplicial join

The covariant order reversal of augmented ordinals exchanges the two
ordinal sum factors. The existing Day convolution universal property
then constructs the reversal of the full original simplicial join.

The construction uses the original Day tensor, including its degree
minus one point. It does not substitute a second join representation.

The mathematical source is Lurie's *Higher Topos Theory*, Definition
1.2.8.1: order reversal exchanges the ordered decomposition factors.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor
  ExternalProduct CategoryTheory.Prod

universe u

namespace AugmentedSimplexCategory

/-- Order reversal on augmented ordinals fixes the empty ordinal. -/
@[implicit_reducible]
def rev : AugmentedSimplexCategory ⥤ AugmentedSimplexCategory where
  obj a := a
  map {a b} f := match a, b, f with
    | .of _, .of _, f => SimplexCategory.rev.map f
    | .star, .of _, _ => PUnit.unit
    | .star, .star, _ => PUnit.unit
  map_id a := by
    cases a with
    | star => rfl
    | of a => exact SimplexCategory.rev.map_id a
  map_comp {a b c} f g := by
    cases a with
    | star =>
      cases c <;> exact Subsingleton.elim _ _
    | of a =>
      cases b with
      | star => exact PEmpty.elim f
      | of b =>
        cases c with
        | star => exact PEmpty.elim g
        | of c => exact SimplexCategory.rev.map_comp f g

@[simp]
lemma rev_obj (a : AugmentedSimplexCategory) : rev.obj a = a := rfl

@[simp]
lemma rev_map_of {a b : SimplexCategory} (f : a ⟶ b) :
    rev.map (show (WithInitial.of a : AugmentedSimplexCategory) ⟶ WithInitial.of b from f) =
      SimplexCategory.rev.map f := rfl

/-- Reversing an augmented ordinal map twice retains the original map. -/
@[simp]
lemma rev_map_rev_map {a b : AugmentedSimplexCategory} (f : a ⟶ b) :
    rev.map (rev.map f) = f := by
  cases a with
  | star => cases b <;> cases f <;> rfl
  | of a =>
    cases b with
    | star => exact PEmpty.elim f
    | of b => exact SimplexCategory.rev_map_rev_map f

/-- The actual covariant order reversal is an involution. -/
def revCompRevIso : rev ⋙ rev ≅ 𝟭 AugmentedSimplexCategory :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    change rev.map (rev.map f) ≫ 𝟙 b = 𝟙 a ≫ f
    simp)

/-- Augmented order reversal as an equivalence of the original category. -/
def revEquivalence : AugmentedSimplexCategory ≌ AugmentedSimplexCategory where
  functor := rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
  functor_unitIso_comp a := by
    change rev.map (𝟙 a) ≫ 𝟙 a = 𝟙 a
    simp

instance : rev.IsEquivalence := revEquivalence.isEquivalence_functor

/-- Reversing an ordinal sum exchanges its two original factors. -/
def revTensorIso (a b : AugmentedSimplexCategory) :
    rev.obj (a ⊗ b) ≅ rev.obj b ⊗ rev.obj a :=
  match a, b with
  | .of a, .of b =>
      WithInitial.incl.mapIso (eqToIso (congrArg SimplexCategory.mk
        (show a.len + b.len + 1 = b.len + a.len + 1 by omega)))
  | .star, .of _ => Iso.refl _
  | .of _, .star => Iso.refl _
  | .star, .star => Iso.refl _

/-- The original first summand becomes the original second summand. -/
@[reassoc]
theorem rev_inl_comp_revTensorIso_hom (a b : AugmentedSimplexCategory) :
    rev.map (inl a b) ≫ (revTensorIso a b).hom = inr (rev.obj b) (rev.obj a) := by
  cases a with
  | star => cases b <;> exact WithInitial.starInitial.hom_ext _ _
  | of a =>
    cases b with
    | star =>
      change rev.map (𝟙 (WithInitial.of a)) ≫ 𝟙 _ = 𝟙 _
      simp only [Category.comp_id]
      change SimplexCategory.rev.map (𝟙 a) = 𝟙 a
      exact SimplexCategory.rev.map_id a
    | of b =>
      change SimplexCategory.rev.map (inl' a b) ≫
        eqToHom (congrArg SimplexCategory.mk
          (show a.len + b.len + 1 = b.len + a.len + 1 by omega)) = inr' b a
      ext i : 3
      simp [inl'_eval, inr'_eval, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.ext_iff]
      omega

/-- The original second summand becomes the original first summand. -/
@[reassoc]
theorem rev_inr_comp_revTensorIso_hom (a b : AugmentedSimplexCategory) :
    rev.map (inr a b) ≫ (revTensorIso a b).hom = inl (rev.obj b) (rev.obj a) := by
  cases b with
  | star => cases a <;> exact WithInitial.starInitial.hom_ext _ _
  | of b =>
    cases a with
    | star =>
      change rev.map (𝟙 (WithInitial.of b)) ≫ 𝟙 _ = 𝟙 _
      simp only [Category.comp_id]
      change SimplexCategory.rev.map (𝟙 b) = 𝟙 b
      exact SimplexCategory.rev.map_id b
    | of a =>
      change SimplexCategory.rev.map (inr' a b) ≫
        eqToHom (congrArg SimplexCategory.mk
          (show a.len + b.len + 1 = b.len + a.len + 1 by omega)) = inl' b a
      ext i : 3
      simp [inl'_eval, inr'_eval, SimplexCategory.comp_toOrderHom,
        SimplexCategory.eqToHom_toOrderHom, Fin.ext_iff]
      omega

/-- The two reversed original inclusions still determine a map from the sum. -/
theorem rev_tensorObj_hom_ext {a b c : AugmentedSimplexCategory}
    (f g : rev.obj (a ⊗ b) ⟶ c)
    (hl : rev.map (inl a b) ≫ f = rev.map (inl a b) ≫ g)
    (hr : rev.map (inr a b) ≫ f = rev.map (inr a b) ≫ g) : f = g := by
  apply rev.map_injective
  apply tensorObj_hom_ext
  · simpa only [rev_obj, Functor.map_comp, rev_map_rev_map] using congrArg rev.map hl
  · simpa only [rev_obj, Functor.map_comp, rev_map_rev_map] using congrArg rev.map hr

/-- The ordinal sum reversal is natural for the two original ordinal maps. -/
@[reassoc]
theorem revTensorIso_hom_naturality {a a' b b' : AugmentedSimplexCategory}
    (f : a ⟶ a') (g : b ⟶ b') :
    rev.map (f ⊗ₘ g) ≫ (revTensorIso a' b').hom =
      (revTensorIso a b).hom ≫ (rev.map g ⊗ₘ rev.map f) := by
  apply rev_tensorObj_hom_ext
  · calc
      rev.map (inl a b) ≫ (rev.map (f ⊗ₘ g) ≫ (revTensorIso a' b').hom) =
          rev.map f ≫ (rev.map (inl a' b') ≫ (revTensorIso a' b').hom) := by
            rw [← Category.assoc, ← Functor.map_comp, inl_comp_tensorHom,
              Functor.map_comp, Category.assoc]
      _ = rev.map f ≫ inr (rev.obj b') (rev.obj a') := by
            rw [rev_inl_comp_revTensorIso_hom]
      _ = inr (rev.obj b) (rev.obj a) ≫ (rev.map g ⊗ₘ rev.map f) :=
            (inr_comp_tensorHom _ _).symm
      _ = rev.map (inl a b) ≫ ((revTensorIso a b).hom ≫
          (rev.map g ⊗ₘ rev.map f)) := by
            rw [← Category.assoc, rev_inl_comp_revTensorIso_hom]
  · calc
      rev.map (inr a b) ≫ (rev.map (f ⊗ₘ g) ≫ (revTensorIso a' b').hom) =
          rev.map g ≫ (rev.map (inr a' b') ≫ (revTensorIso a' b').hom) := by
            rw [← Category.assoc, ← Functor.map_comp, inr_comp_tensorHom,
              Functor.map_comp, Category.assoc]
      _ = rev.map g ≫ inl (rev.obj b') (rev.obj a') := by
            rw [rev_inr_comp_revTensorIso_hom]
      _ = inl (rev.obj b) (rev.obj a) ≫ (rev.map g ⊗ₘ rev.map f) :=
            (inl_comp_tensorHom _ _).symm
      _ = rev.map (inr a b) ≫ ((revTensorIso a b).hom ≫
          (rev.map g ⊗ₘ rev.map f)) := by
            rw [← Category.assoc, rev_inr_comp_revTensorIso_hom]

end AugmentedSimplexCategory

namespace SSet.Join

/-- The original reversal functor on opposite augmented ordinals. -/
abbrev reverseOrdinal : AugmentedSimplexCategoryᵒᵖ ⥤
    AugmentedSimplexCategoryᵒᵖ := AugmentedSimplexCategory.rev.op

/-- Reverse an actual augmented presheaf, retaining its degree minus one value. -/
def reverseDay (F : DayCat.{u}) : DayCat.{u} :=
  DayFunctor.mk (reverseOrdinal ⋙ F.functor)

/-- Reverse and exchange the two original indexing ordinals. -/
def reversePair : AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ ⥤
    AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ :=
  CategoryTheory.Prod.swap _ _ ⋙ reverseOrdinal.prod reverseOrdinal

instance : reversePair.IsEquivalence := by
  exact ((CategoryTheory.Prod.braiding AugmentedSimplexCategoryᵒᵖ
    AugmentedSimplexCategoryᵒᵖ).trans
      (AugmentedSimplexCategory.revEquivalence.op.prod
        AugmentedSimplexCategory.revEquivalence.op)).isEquivalence_functor

/-- The actual ordinal sum comparison for the reversed pair. -/
def reverseSumIso :
    reversePair ⋙ tensor AugmentedSimplexCategoryᵒᵖ ≅
      tensor AugmentedSimplexCategoryᵒᵖ ⋙ reverseOrdinal :=
  NatIso.ofComponents
    (fun p => (AugmentedSimplexCategory.revTensorIso p.1.unop p.2.unop).op)
    (by
      intro p q f
      apply Quiver.Hom.unop_inj
      change (AugmentedSimplexCategory.revTensorIso q.1.unop q.2.unop).hom ≫
          (AugmentedSimplexCategory.rev.map f.2.unop ⊗ₘ
            AugmentedSimplexCategory.rev.map f.1.unop) =
        AugmentedSimplexCategory.rev.map (f.1.unop ⊗ₘ f.2.unop) ≫
          (AugmentedSimplexCategory.revTensorIso p.1.unop p.2.unop).hom
      exact (AugmentedSimplexCategory.revTensorIso_hom_naturality
        f.1.unop f.2.unop).symm)

/-- The actual input pair of elements is exchanged before the original Day unit. -/
def reverseInputIso (F G : DayCat.{u}) :
    (reverseDay G).functor ⊠ (reverseDay F).functor ≅
      reversePair ⋙ (F.functor ⊠ G.functor) :=
  NatIso.ofComponents (fun _ => (Equiv.prodComm _ _).toIso) (by
    intro p q f
    ext x
    rfl)

/-- The original Day extension unit, transported through the actual ordinal reversal. -/
def reverseUnit (F G : DayCat.{u}) :
    (reverseDay G).functor ⊠ (reverseDay F).functor ⟶
      tensor AugmentedSimplexCategoryᵒᵖ ⋙ (reverseDay (F ⊗ G)).functor :=
  (reverseInputIso F G).hom ≫
    Functor.whiskerLeft reversePair (DayFunctor.η F G) ≫
    (Functor.associator reversePair (tensor AugmentedSimplexCategoryᵒᵖ)
      (F ⊗ G).functor).inv ≫
    Functor.whiskerRight reverseSumIso.hom (F ⊗ G).functor ≫
    (Functor.associator (tensor AugmentedSimplexCategoryᵒᵖ) reverseOrdinal
      (F ⊗ G).functor).hom

/-- Equivalences of the original indexing categories preserve this actual Kan extension. -/
theorem reverseUnit_isLeftKanExtension (F G : DayCat.{u}) :
    (reverseDay (F ⊗ G)).functor.IsLeftKanExtension (reverseUnit F G) := by
  exact (Functor.isLeftKanExtension_iff_precomp_equivalence
    (reverseUnit F G) (DayFunctor.η F G) reverseSumIso
    (reverseInputIso F G) (Iso.refl _) (by
      ext p x
      rfl)).mp inferInstance

/-- The two original Kan extension units determine the full reversed tensor isomorphism. -/
def reverseTensorIso (F G : DayCat.{u}) :
    (reverseDay (F ⊗ G)).functor ≅ (reverseDay G ⊗ reverseDay F).functor := by
  letI := reverseUnit_isLeftKanExtension F G
  exact Functor.leftKanExtensionUnique (reverseDay (F ⊗ G)).functor
    (reverseUnit F G) (reverseDay G ⊗ reverseDay F).functor
    (DayFunctor.η (reverseDay G) (reverseDay F))

/-- The original reversed extension unit is the unit of the reversed tensor under the comparison. -/
theorem reverseUnit_comp_reverseTensorIso_hom (F G : DayCat.{u}) :
    reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      (reverseTensorIso F G).hom = DayFunctor.η (reverseDay G) (reverseDay F) := by
  let := reverseUnit_isLeftKanExtension F G
  change reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
    ((reverseDay (F ⊗ G)).functor.descOfIsLeftKanExtension (reverseUnit F G)
      (reverseDay G ⊗ reverseDay F).functor (DayFunctor.η (reverseDay G) (reverseDay F))) = _
  exact Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- The original Day functor equivalence reflects an isomorphism of underlying presheaves. -/
def dayIsoOfNatIso {F G : DayCat.{u}} (e : F.functor ≅ G.functor) : F ≅ G where
  hom := DayFunctor.Hom.mk e.hom
  inv := DayFunctor.Hom.mk e.inv
  hom_inv_id := by
    apply DayFunctor.hom_ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply DayFunctor.hom_ext
    exact e.inv_hom_id

/-- The same original tensor isomorphism in the Day functor category. -/
def reverseTensorDayIso (F G : DayCat.{u}) :
    reverseDay (F ⊗ G) ≅ reverseDay G ⊗ reverseDay F :=
  dayIsoOfNatIso (reverseTensorIso F G)

/-- Augmenting the original opposite simplicial set agrees with reversing its augmented presheaf. -/
def augReverseIso (X : SSet.{u}) :
    reverseOrdinal ⋙ aug.obj X ≅ aug.obj X.op :=
  NatIso.ofComponents
    (fun n => WithInitial.rec
      (motive := fun a : AugmentedSimplexCategory =>
        (reverseOrdinal ⋙ aug.obj X).obj (op a) ≅ (aug.obj X.op).obj (op a))
      (fun k => (SSet.opObjEquiv (X := X) (n := op k)).symm.toIso)
      (Iso.refl _) n.unop)
    (by
      intro n m f
      obtain ⟨a, rfl⟩ : ∃ a, n = op a := ⟨n.unop, rfl⟩
      obtain ⟨b, rfl⟩ : ∃ b, m = op b := ⟨m.unop, rfl⟩
      cases a with
      | star =>
        cases b with
        | star => rfl
        | of b => exact (WithInitial.false_of_to_star f.unop).elim
      | of a =>
        cases b with
        | star => exact Types.isTerminalPUnit.hom_ext _ _
        | of b =>
          ext x
          rfl)

/-- The augmented opposite comparison in the original Day functor category. -/
def augDayReverseIso (X : SSet.{u}) :
    reverseDay (augDay.obj X) ≅ augDay.obj X.op :=
  dayIsoOfNatIso (augReverseIso X)

/-- Dropping the degree minus one value commutes with the actual order reversal. -/
def dropDayReverseIso (F : DayCat.{u}) :
    (dropDay.obj F).op ≅ dropDay.obj (reverseDay F) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    ext x
    rfl)

/-- Reversal acts on every original presheaf map by precomposition. -/
@[implicit_reducible]
def reverseDayFunctor : DayCat.{u} ⥤ DayCat.{u} where
  obj := reverseDay
  map f := DayFunctor.Hom.mk (Functor.whiskerLeft reverseOrdinal f.natTrans)
  map_id _ := by
    apply DayFunctor.hom_ext
    rfl
  map_comp _ _ := by
    apply DayFunctor.hom_ext
    rfl

/-- The two original presheaf maps act on the input of the Day extension. -/
def dayTensorInputMap {F F' G G' : DayCat.{u}} (f : F ⟶ F') (g : G ⟶ G') :
    F.functor ⊠ G.functor ⟶ F'.functor ⊠ G'.functor :=
  (externalProductBifunctor _ _ (Type u)).map (f.natTrans ×ₘ g.natTrans)

/-- The original Day unit is natural in both original presheaves. -/
theorem η_tensorHom_app {F F' G G' : DayCat.{u}} (f : F ⟶ F') (g : G ⟶ G')
    (a b : AugmentedSimplexCategoryᵒᵖ) :
    (DayFunctor.η F G).app (a, b) ≫ (f ⊗ₘ g).natTrans.app (a ⊗ b) =
      (f.natTrans.app a ⊗ₘ g.natTrans.app b) ≫ (DayFunctor.η F' G').app (a, b) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
    AugmentedSimplexCategoryᵒᵖ (Type u) f g a b

/-- The whole original extension unit is natural for the input maps. -/
theorem η_tensorHom {F F' G G' : DayCat.{u}} (f : F ⟶ F') (g : G ⟶ G') :
    DayFunctor.η F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      (f ⊗ₘ g).natTrans = dayTensorInputMap f g ≫ DayFunctor.η F' G' := by
  apply NatTrans.ext
  funext p
  rcases p with ⟨a, b⟩
  exact η_tensorHom_app f g a b

/-- Reversing the original extension unit also reverses the order of its input maps. -/
theorem reverseUnit_naturality {F F' G G' : DayCat.{u}} (f : F ⟶ F') (g : G ⟶ G') :
    dayTensorInputMap (reverseDayFunctor.map g) (reverseDayFunctor.map f) ≫
        reverseUnit F' G' =
      reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
        (reverseDayFunctor.map (f ⊗ₘ g)).natTrans := by
  apply NatTrans.ext
  funext p
  rcases p with ⟨a, b⟩
  apply ConcreteCategory.hom_ext
  intro x
  let ordMap := (reverseSumIso.app (a, b)).hom
  let z := (DayFunctor.η F G).app (reverseOrdinal.obj b, reverseOrdinal.obj a) (x.2, x.1)
  have hm := types_congr_hom ((f ⊗ₘ g).natTrans.naturality ordMap) z
  have he : (f ⊗ₘ g).natTrans.app (reverseOrdinal.obj b ⊗ reverseOrdinal.obj a) z =
      (DayFunctor.η F' G').app (reverseOrdinal.obj b, reverseOrdinal.obj a)
        (f.natTrans.app (reverseOrdinal.obj b) x.2,
          g.natTrans.app (reverseOrdinal.obj a) x.1) :=
    types_congr_hom (η_tensorHom_app f g (reverseOrdinal.obj b) (reverseOrdinal.obj a))
      (x.2, x.1)
  change (F' ⊗ G').functor.map ordMap
      ((DayFunctor.η F' G').app (reverseOrdinal.obj b, reverseOrdinal.obj a)
        (f.natTrans.app (reverseOrdinal.obj b) x.2,
          g.natTrans.app (reverseOrdinal.obj a) x.1)) =
    (f ⊗ₘ g).natTrans.app (reverseOrdinal.obj (a ⊗ b)) ((F ⊗ G).functor.map ordMap z)
  exact (hm.trans (congrArg ((F' ⊗ G').functor.map ordMap) he)).symm

/-- The original reversed tensor comparison is natural in both presheaf maps. -/
theorem reverseTensorDayIso_hom_naturality {F F' G G' : DayCat.{u}}
    (f : F ⟶ F') (g : G ⟶ G') :
    reverseDayFunctor.map (f ⊗ₘ g) ≫ (reverseTensorDayIso F' G').hom =
      (reverseTensorDayIso F G).hom ≫
        (reverseDayFunctor.map g ⊗ₘ reverseDayFunctor.map f) := by
  apply DayFunctor.hom_ext
  let := reverseUnit_isLeftKanExtension F G
  apply Functor.hom_ext_of_isLeftKanExtension (reverseDay (F ⊗ G)).functor
    (reverseUnit F G)
  change reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      ((reverseDayFunctor.map (f ⊗ₘ g)).natTrans ≫ (reverseTensorIso F' G').hom) =
    reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
      ((reverseTensorIso F G).hom ≫
        (reverseDayFunctor.map g ⊗ₘ reverseDayFunctor.map f).natTrans)
  calc
    reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
        ((reverseDayFunctor.map (f ⊗ₘ g)).natTrans ≫ (reverseTensorIso F' G').hom) =
      (reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
        (reverseDayFunctor.map (f ⊗ₘ g)).natTrans) ≫
          Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
            (reverseTensorIso F' G').hom := by
              ext p x
              rfl
    _ = (dayTensorInputMap (reverseDayFunctor.map g) (reverseDayFunctor.map f) ≫
        reverseUnit F' G') ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
          (reverseTensorIso F' G').hom := by rw [reverseUnit_naturality]
    _ = dayTensorInputMap (reverseDayFunctor.map g) (reverseDayFunctor.map f) ≫
        DayFunctor.η (reverseDay G') (reverseDay F') := by
          rw [Category.assoc, reverseUnit_comp_reverseTensorIso_hom]
    _ = DayFunctor.η (reverseDay G) (reverseDay F) ≫
        Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
          (reverseDayFunctor.map g ⊗ₘ reverseDayFunctor.map f).natTrans :=
            (η_tensorHom (reverseDayFunctor.map g) (reverseDayFunctor.map f)).symm
    _ = reverseUnit F G ≫ Functor.whiskerLeft (tensor AugmentedSimplexCategoryᵒᵖ)
        ((reverseTensorIso F G).hom ≫
          (reverseDayFunctor.map g ⊗ₘ reverseDayFunctor.map f).natTrans) := by
            rw [← reverseUnit_comp_reverseTensorIso_hom F G]
            ext p x
            rfl

/-- The actual augmentation reversal is natural for every original simplicial map. -/
theorem augDayReverseIso_hom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    reverseDayFunctor.map (augDay.map f) ≫ (augDayReverseIso Y).hom =
      (augDayReverseIso X).hom ≫ augDay.map (opFunctor.map f) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext n
  obtain ⟨a, rfl⟩ : ∃ a, n = op a := ⟨n.unop, rfl⟩
  cases a with
  | star => exact Types.isTerminalPUnit.hom_ext _ _
  | of a =>
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- Dropping the augmentation retains reversal naturality for every presheaf map. -/
theorem dropDayReverseIso_hom_naturality {F G : DayCat.{u}} (f : F ⟶ G) :
    opFunctor.map (dropDay.map f) ≫ (dropDayReverseIso G).hom =
      (dropDayReverseIso F).hom ≫ dropDay.map (reverseDayFunctor.map f) := by
  ext n x
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original right unit inverse is the original Day unit with its degree minus one point. -/
theorem rightUnitor_inv_app (F : DayCat.{u}) (a : SimplexCategory)
    (x : F.functor.obj (op (WithInitial.of a))) :
    (ρ_ F).inv.natTrans.app (op (WithInitial.of a)) x =
      (DayFunctor.η F (𝟙_ DayCat.{u})).app
        (op (WithInitial.of a), op WithInitial.star)
        (x, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  let t := (DayFunctor.η F (𝟙_ DayCat.{u})).app (p, op WithInitial.star)
    (x, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)
  have hp : (ρ_ p).inv = 𝟙 p := rfl
  have ht : (ρ_ F).hom.natTrans.app p t = x := by
    have hs : (F.functor.obj p ◁ DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)) ≫
        (DayFunctor.η F (𝟙_ DayCat.{u})).app (p, op WithInitial.star) ≫
          (ρ_ F).hom.natTrans.app p =
      (ρ_ (F.functor.obj p)).hom ≫ F.functor.map (ρ_ p).inv :=
      LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app (Type u) F p
    have h := types_congr_hom
      hs (x, PUnit.unit)
    have hv : (F.functor.obj p ◁ DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u))
        (x, PUnit.unit) =
      (x, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) :=
      CategoryTheory.whiskerLeft_apply _ _ _
    have hu : (ρ_ (F.functor.obj p)).hom (x, PUnit.unit) = x :=
      CategoryTheory.rightUnitor_hom_apply
    have hm : F.functor.map (𝟙 p) x = x := by
      rw [CategoryTheory.Functor.map_id]
      exact types_id_apply _ _
    simp only [comp_apply] at h
    rw [hv, hu] at h
    exact h.trans hm
  have hi : (ρ_ F).inv.natTrans.app p ((ρ_ F).hom.natTrans.app p t) = t :=
    congrArg (fun k => k.natTrans.app p t) (ρ_ F).hom_inv_id
  exact (congrArg ((ρ_ F).inv.natTrans.app p) ht).symm.trans hi

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original left unit inverse inserts the same original degree minus one point. -/
theorem leftUnitor_inv_app (F : DayCat.{u}) (a : SimplexCategory)
    (x : F.functor.obj (op (WithInitial.of a))) :
    (λ_ F).inv.natTrans.app (op (WithInitial.of a)) x =
      (DayFunctor.η (𝟙_ DayCat.{u}) F).app
        (op WithInitial.star, op (WithInitial.of a))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, x) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  let t := (DayFunctor.η (𝟙_ DayCat.{u}) F).app (op WithInitial.star, p)
    (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, x)
  have hp : (λ_ p).inv = 𝟙 p := rfl
  have ht : (λ_ F).hom.natTrans.app p t = x := by
    have hs : (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) ▷ F.functor.obj p) ≫
        (DayFunctor.η (𝟙_ DayCat.{u}) F).app (op WithInitial.star, p) ≫
          (λ_ F).hom.natTrans.app p =
      (λ_ (F.functor.obj p)).hom ≫ F.functor.map (λ_ p).inv :=
      LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app (Type u) F p
    have h := types_congr_hom
      hs (PUnit.unit, x)
    have hv : (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) ▷ F.functor.obj p)
        (PUnit.unit, x) =
      (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, x) :=
      CategoryTheory.whiskerRight_apply _ _ _
    have hu : (λ_ (F.functor.obj p)).hom (PUnit.unit, x) = x :=
      CategoryTheory.leftUnitor_hom_apply
    have hm : F.functor.map (𝟙 p) x = x := by
      rw [CategoryTheory.Functor.map_id]
      exact types_id_apply _ _
    simp only [comp_apply] at h
    rw [hv, hu] at h
    exact h.trans hm
  have hi : (λ_ F).inv.natTrans.app p ((λ_ F).hom.natTrans.app p t) = t :=
    congrArg (fun k => k.natTrans.app p t) (λ_ F).hom_inv_id
  exact (congrArg ((λ_ F).inv.natTrans.app p) ht).symm.trans hi

/-- The literal first join inclusion is the actual right unit and its three augmented maps. -/
theorem _root_.SSet.joinInl_eq_dropDay (X Y : SSet.{u}) :
    joinInl X Y = Join.dropDay.map
      ((ρ_ (Join.augDay.obj X)).inv ≫
        (Join.augDay.obj X ◁ Join.dayUnitYonedaIso.hom) ≫
        (Join.augDay.obj X ◁ Join.augDayBotIso.inv) ≫
        (Join.augDay.obj X ◁ Join.augDay.map (initial.to Y))) := by
  simp only [SSet.joinInl, SSet.joinBotIso, SSet.join_obj_map_eq,
    Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
    id_tensorHom, Functor.map_comp, Category.assoc]
  rfl

/-- The literal second join inclusion is the actual left unit
and the corresponding augmented maps. -/
theorem _root_.SSet.joinInr_eq_dropDay (X Y : SSet.{u}) :
    joinInr X Y = Join.dropDay.map
      ((λ_ (Join.augDay.obj Y)).inv ≫
        (Join.dayUnitYonedaIso.hom ▷ Join.augDay.obj Y) ≫
        (Join.augDayBotIso.inv ▷ Join.augDay.obj Y) ≫
        (Join.augDay.map (initial.to X) ▷ Join.augDay.obj Y)) := by
  simp only [SSet.joinInr, SSet.botJoinIso, SSet.join_map_app_eq,
    Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
    tensorHom_id, Functor.map_comp, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An original right input map acts on the original Day unit element. -/
theorem η_whiskerLeft_point (F G G' : DayCat.{u}) (α : G ⟶ G')
    (a : SimplexCategory) (x : F.functor.obj (op (WithInitial.of a)))
    (y : G.functor.obj (op WithInitial.star)) :
    (F ◁ α).natTrans.app (op (WithInitial.of a))
        ((DayFunctor.η F G).app (op (WithInitial.of a), op WithInitial.star) (x, y)) =
      (DayFunctor.η F G').app (op (WithInitial.of a), op WithInitial.star)
        (x, α.natTrans.app (op WithInitial.star) y) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  have hs : (DayFunctor.η F G).app (p, op WithInitial.star) ≫ (F ◁ α).natTrans.app p =
      (F.functor.obj p ◁ α.natTrans.app (op WithInitial.star)) ≫
        (DayFunctor.η F G').app (p, op WithInitial.star) :=
    η_whiskerLeft_app F G G' α p (op WithInitial.star)
  have h := types_congr_hom hs (x, y)
  have hv : (F.functor.obj p ◁ α.natTrans.app (op WithInitial.star)) (x, y) =
      (x, α.natTrans.app (op WithInitial.star) y) :=
    CategoryTheory.whiskerLeft_apply _ _ _
  simp only [comp_apply] at h
  exact h.trans (congrArg ((DayFunctor.η F G').app (p, op WithInitial.star)) hv)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An original left input map acts on the original Day unit element. -/
theorem η_whiskerRight_point (F F' G : DayCat.{u}) (α : F ⟶ F')
    (a : SimplexCategory) (x : F.functor.obj (op WithInitial.star))
    (y : G.functor.obj (op (WithInitial.of a))) :
    (α ▷ G).natTrans.app (op (WithInitial.of a))
        ((DayFunctor.η F G).app (op WithInitial.star, op (WithInitial.of a)) (x, y)) =
      (DayFunctor.η F' G).app (op WithInitial.star, op (WithInitial.of a))
        (α.natTrans.app (op WithInitial.star) x, y) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  have hs : (DayFunctor.η F G).app (op WithInitial.star, p) ≫ (α ▷ G).natTrans.app p =
      (α.natTrans.app (op WithInitial.star) ▷ G.functor.obj p) ≫
        (DayFunctor.η F' G).app (op WithInitial.star, p) :=
    η_whiskerRight_app F F' G α (op WithInitial.star) p
  have h := types_congr_hom hs (x, y)
  have hv : (α.natTrans.app (op WithInitial.star) ▷ G.functor.obj p) (x, y) =
      (α.natTrans.app (op WithInitial.star) x, y) :=
    CategoryTheory.whiskerRight_apply _ _ _
  simp only [comp_apply] at h
  exact h.trans (congrArg ((DayFunctor.η F' G).app (op WithInitial.star, p)) hv)

/-- The original first inclusion inserts precisely the original degree minus one point. -/
theorem _root_.SSet.joinInl_app_eq_η (X Y : SSet.{u}) (a : SimplexCategory)
    (x : X.obj (op a)) :
    (joinInl X Y).app (op a) x =
      (DayFunctor.η (Join.augDay.obj X) (Join.augDay.obj Y)).app
        (op (WithInitial.of a), op WithInitial.star) (x, PUnit.unit) := by
  let F := Join.augDay.obj X
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  rw [SSet.joinInl_eq_dropDay]
  change (F ◁ Join.augDay.map (initial.to Y)).natTrans.app p
      ((F ◁ Join.augDayBotIso.inv).natTrans.app p
        ((F ◁ Join.dayUnitYonedaIso.hom).natTrans.app p ((ρ_ F).inv.natTrans.app p x))) = _
  have h₁ : (F ◁ Join.dayUnitYonedaIso.hom).natTrans.app p
      ((DayFunctor.η F (𝟙_ DayCat.{u})).app (p, op WithInitial.star)
        (x, DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)) =
      (DayFunctor.η F (Join.dayYoneda WithInitial.star)).app (p, op WithInitial.star)
        (x, ULift.up (𝟙 WithInitial.star)) := by
    have h :=
      Join.η_whiskerLeft_point F (𝟙_ DayCat.{u}) (Join.dayYoneda WithInitial.star)
        Join.dayUnitYonedaIso.hom a x (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)
    exact h.trans (congrArg (fun z => (DayFunctor.η F (Join.dayYoneda WithInitial.star)).app
      (p, op WithInitial.star) (x, z)) Join.dayUnitYonedaIso_hom_app_ν)
  have h₂ : (F ◁ Join.augDayBotIso.inv).natTrans.app p
      ((DayFunctor.η F (Join.dayYoneda WithInitial.star)).app (p, op WithInitial.star)
        (x, ULift.up (𝟙 WithInitial.star))) =
      (DayFunctor.η F (Join.augDay.obj (⊥_ SSet.{u}))).app (p, op WithInitial.star)
        (x, PUnit.unit) := by
    have h :=
      Join.η_whiskerLeft_point F (Join.dayYoneda WithInitial.star)
        (Join.augDay.obj (⊥_ SSet.{u})) Join.augDayBotIso.inv a x (ULift.up (𝟙 WithInitial.star))
    exact h.trans (congrArg (fun z => (DayFunctor.η F (Join.augDay.obj (⊥_ SSet.{u}))).app
      (p, op WithInitial.star) (x, z)) Join.augDayBotIso_inv_app_star)
  have h₃ : (F ◁ Join.augDay.map (initial.to Y)).natTrans.app p
      ((DayFunctor.η F (Join.augDay.obj (⊥_ SSet.{u}))).app (p, op WithInitial.star)
        (x, PUnit.unit)) =
      (DayFunctor.η F (Join.augDay.obj Y)).app (p, op WithInitial.star)
        (x, PUnit.unit) := by
    have h :=
      Join.η_whiskerLeft_point F (Join.augDay.obj (⊥_ SSet.{u})) (Join.augDay.obj Y)
        (Join.augDay.map (initial.to Y)) a x PUnit.unit
    exact h.trans (congrArg (fun z => (DayFunctor.η F (Join.augDay.obj Y)).app
      (p, op WithInitial.star) (x, z)) Join.augDay_map_initial_to_app_star)
  rw [Join.rightUnitor_inv_app F a x, h₁, h₂, h₃]

/-- The original second inclusion uses that same point in the first input position. -/
theorem _root_.SSet.joinInr_app_eq_η (X Y : SSet.{u}) (a : SimplexCategory)
    (y : Y.obj (op a)) :
    (joinInr X Y).app (op a) y =
      (DayFunctor.η (Join.augDay.obj X) (Join.augDay.obj Y)).app
        (op WithInitial.star, op (WithInitial.of a)) (PUnit.unit, y) := by
  let G := Join.augDay.obj Y
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  rw [SSet.joinInr_eq_dropDay]
  change (Join.augDay.map (initial.to X) ▷ G).natTrans.app p
      ((Join.augDayBotIso.inv ▷ G).natTrans.app p
        ((Join.dayUnitYonedaIso.hom ▷ G).natTrans.app p ((λ_ G).inv.natTrans.app p y))) = _
  have h₁ : (Join.dayUnitYonedaIso.hom ▷ G).natTrans.app p
      ((DayFunctor.η (𝟙_ DayCat.{u}) G).app (op WithInitial.star, p)
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit, y)) =
      (DayFunctor.η (Join.dayYoneda WithInitial.star) G).app (op WithInitial.star, p)
        (ULift.up (𝟙 WithInitial.star), y) := by
    have h :=
      Join.η_whiskerRight_point (𝟙_ DayCat.{u}) (Join.dayYoneda WithInitial.star) G
        Join.dayUnitYonedaIso.hom a (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) y
    exact h.trans (congrArg (fun z => (DayFunctor.η (Join.dayYoneda WithInitial.star) G).app
      (op WithInitial.star, p) (z, y)) Join.dayUnitYonedaIso_hom_app_ν)
  have h₂ : (Join.augDayBotIso.inv ▷ G).natTrans.app p
      ((DayFunctor.η (Join.dayYoneda WithInitial.star) G).app (op WithInitial.star, p)
        (ULift.up (𝟙 WithInitial.star), y)) =
      (DayFunctor.η (Join.augDay.obj (⊥_ SSet.{u})) G).app (op WithInitial.star, p)
        (PUnit.unit, y) := by
    have h :=
      Join.η_whiskerRight_point (Join.dayYoneda WithInitial.star)
        (Join.augDay.obj (⊥_ SSet.{u})) G Join.augDayBotIso.inv a (ULift.up (𝟙 WithInitial.star)) y
    exact h.trans (congrArg (fun z => (DayFunctor.η (Join.augDay.obj (⊥_ SSet.{u})) G).app
      (op WithInitial.star, p) (z, y)) Join.augDayBotIso_inv_app_star)
  have h₃ : (Join.augDay.map (initial.to X) ▷ G).natTrans.app p
      ((DayFunctor.η (Join.augDay.obj (⊥_ SSet.{u})) G).app (op WithInitial.star, p)
        (PUnit.unit, y)) =
      (DayFunctor.η (Join.augDay.obj X) G).app (op WithInitial.star, p)
        (PUnit.unit, y) := by
    have h :=
      Join.η_whiskerRight_point (Join.augDay.obj (⊥_ SSet.{u})) (Join.augDay.obj X) G
        (Join.augDay.map (initial.to X)) a PUnit.unit y
    exact h.trans (congrArg (fun z => (DayFunctor.η (Join.augDay.obj X) G).app
      (op WithInitial.star, p) (z, y)) Join.augDay_map_initial_to_app_star)
  rw [Join.leftUnitor_inv_app G a y, h₁, h₂, h₃]

/-- The reversed original Day unit exchanges its two actual input elements. -/
theorem reverseTensorDayIso_hom_η (F G : DayCat.{u})
    (a b : AugmentedSimplexCategoryᵒᵖ)
    (x : F.functor.obj (reverseOrdinal.obj b))
    (y : G.functor.obj (reverseOrdinal.obj a)) :
    (reverseTensorDayIso F G).hom.natTrans.app (a ⊗ b)
        ((F ⊗ G).functor.map (reverseSumIso.app (a, b)).hom
          ((DayFunctor.η F G).app (reverseOrdinal.obj b, reverseOrdinal.obj a) (x, y))) =
      (DayFunctor.η (reverseDay G) (reverseDay F)).app (a, b) (y, x) := by
  have h := types_congr_hom
    (NatTrans.congr_app (reverseUnit_comp_reverseTensorIso_hom F G) (a, b)) (y, x)
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original first factor unit becomes the original second factor unit. -/
theorem reverseTensorDayIso_hom_leftPoint (F G : DayCat.{u}) (a : SimplexCategory)
    (x : F.functor.obj (op (WithInitial.of a)))
    (y : G.functor.obj (op WithInitial.star)) :
    (reverseTensorDayIso F G).hom.natTrans.app (op (WithInitial.of a))
        ((DayFunctor.η F G).app (op (WithInitial.of a), op WithInitial.star) (x, y)) =
      (DayFunctor.η (reverseDay G) (reverseDay F)).app
        (op WithInitial.star, op (WithInitial.of a)) (y, x) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  have hc : (reverseUnit F G).app (op WithInitial.star, p) ≫
        (reverseTensorIso F G).hom.app p =
      (DayFunctor.η (reverseDay G) (reverseDay F)).app (op WithInitial.star, p) :=
    NatTrans.congr_app (reverseUnit_comp_reverseTensorIso_hom F G) (op WithInitial.star, p)
  have hb : (reverseUnit F G).app (op WithInitial.star, p) (y, x) =
      (DayFunctor.η F G).app (p, op WithInitial.star) (x, y) := by
    change (F ⊗ G).functor.map (𝟙 p)
      ((DayFunctor.η F G).app (p, op WithInitial.star) (x, y)) = _
    rw [CategoryTheory.Functor.map_id]
    exact types_id_apply _ _
  have h := types_congr_hom hc (y, x)
  simp only [comp_apply] at h
  rw [hb] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original second factor unit becomes the original first factor unit. -/
theorem reverseTensorDayIso_hom_rightPoint (F G : DayCat.{u}) (a : SimplexCategory)
    (x : F.functor.obj (op WithInitial.star))
    (y : G.functor.obj (op (WithInitial.of a))) :
    (reverseTensorDayIso F G).hom.natTrans.app (op (WithInitial.of a))
        ((DayFunctor.η F G).app (op WithInitial.star, op (WithInitial.of a)) (x, y)) =
      (DayFunctor.η (reverseDay G) (reverseDay F)).app
        (op (WithInitial.of a), op WithInitial.star) (y, x) := by
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  have hc : (reverseUnit F G).app (p, op WithInitial.star) ≫
        (reverseTensorIso F G).hom.app p =
      (DayFunctor.η (reverseDay G) (reverseDay F)).app (p, op WithInitial.star) :=
    NatTrans.congr_app (reverseUnit_comp_reverseTensorIso_hom F G) (p, op WithInitial.star)
  have hb : (reverseUnit F G).app (p, op WithInitial.star) (y, x) =
      (DayFunctor.η F G).app (op WithInitial.star, p) (x, y) := by
    change (F ⊗ G).functor.map (𝟙 p)
      ((DayFunctor.η F G).app (op WithInitial.star, p) (x, y)) = _
    rw [CategoryTheory.Functor.map_id]
    exact types_id_apply _ _
  have h := types_congr_hom hc (y, x)
  simp only [comp_apply] at h
  rw [hb] at h
  exact h

/-- In every original degree the augmentation comparison retains the original opposite simplex. -/
@[simp]
theorem augDayReverseIso_hom_app_of (X : SSet.{u}) (a : SimplexCategory)
    (x : X.obj (op a)) :
    (augDayReverseIso X).hom.natTrans.app (op (WithInitial.of a)) x =
      SSet.opObjEquiv.symm x := rfl

/-- The original augmentation point is fixed by the actual comparison. -/
@[simp]
theorem augDayReverseIso_hom_app_star (X : SSet.{u}) :
    (augDayReverseIso X).hom.natTrans.app (op WithInitial.star) PUnit.unit = PUnit.unit :=
  rfl

/-- Order reversal exchanges the two factors of the full original simplicial join. -/
def _root_.SSet.joinOppositeIso (X Y : SSet.{u}) : (X ⋆ Y).op ≅ Y.op ⋆ X.op :=
  Join.dropDayReverseIso (Join.augDay.obj X ⊗ Join.augDay.obj Y) ≪≫
    Join.dropDay.mapIso (Join.reverseTensorDayIso (Join.augDay.obj X) (Join.augDay.obj Y)) ≪≫
    Join.dropDay.mapIso (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X))

/-- The two original join maps are the actual tensor of their augmented maps. -/
theorem _root_.SSet.join_bimap_eq {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (join.map f).app Y ≫ (join.obj X').map g =
      Join.dropDay.map (Join.augDay.map f ⊗ₘ Join.augDay.map g) := by
  rw [SSet.join_map_app_eq, SSet.join_obj_map_eq]
  change Join.dropDay.map (Join.augDay.map f ▷ Join.augDay.obj Y) ≫
      Join.dropDay.map (Join.augDay.obj X' ◁ Join.augDay.map g) =
    Join.dropDay.map (Join.augDay.map f ⊗ₘ Join.augDay.map g)
  rw [← Join.dropDay.map_comp, ← tensorHom_def]

/-- Reversal of the full original join is natural for both original simplicial maps. -/
@[reassoc]
theorem _root_.SSet.joinOppositeIso_hom_naturality {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    opFunctor.map ((join.map f).app Y ≫ (join.obj X').map g) ≫
        (joinOppositeIso X' Y').hom =
      (joinOppositeIso X Y).hom ≫
        ((join.map (opFunctor.map g)).app X.op ≫
          (join.obj Y'.op).map (opFunctor.map f)) := by
  rw [SSet.join_bimap_eq f g,
    SSet.join_bimap_eq (opFunctor.map g) (opFunctor.map f)]
  let F := Join.augDay.obj X
  let F' := Join.augDay.obj X'
  let G := Join.augDay.obj Y
  let G' := Join.augDay.obj Y'
  let fD := Join.augDay.map f
  let gD := Join.augDay.map g
  let E := Join.reverseTensorDayIso F G
  let E' := Join.reverseTensorDayIso F' G'
  let A := tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)
  let A' := tensorIso (Join.augDayReverseIso Y') (Join.augDayReverseIso X')
  let fR := Join.reverseDayFunctor.map (fD ⊗ₘ gD)
  let hR := Join.reverseDayFunctor.map gD ⊗ₘ Join.reverseDayFunctor.map fD
  let hO := Join.augDay.map (opFunctor.map g) ⊗ₘ Join.augDay.map (opFunctor.map f)
  have hA : hR ≫ A'.hom = A.hom ≫ hO := by
    change (Join.reverseDayFunctor.map gD ⊗ₘ Join.reverseDayFunctor.map fD) ≫
        ((Join.augDayReverseIso Y').hom ⊗ₘ (Join.augDayReverseIso X').hom) =
      ((Join.augDayReverseIso Y).hom ⊗ₘ (Join.augDayReverseIso X).hom) ≫ hO
    rw [tensorHom_comp_tensorHom, Join.augDayReverseIso_hom_naturality g,
      Join.augDayReverseIso_hom_naturality f, ← tensorHom_comp_tensorHom]
  have hT : fR ≫ E'.hom = E.hom ≫ hR :=
    Join.reverseTensorDayIso_hom_naturality fD gD
  have hD : opFunctor.map (Join.dropDay.map (fD ⊗ₘ gD)) ≫
        (Join.dropDayReverseIso (F' ⊗ G')).hom =
      (Join.dropDayReverseIso (F ⊗ G)).hom ≫ Join.dropDay.map fR :=
    Join.dropDayReverseIso_hom_naturality (fD ⊗ₘ gD)
  have hT' : Join.dropDay.map fR ≫ Join.dropDay.map E'.hom =
      Join.dropDay.map E.hom ≫ Join.dropDay.map hR := by
    simpa only [Functor.map_comp] using congrArg Join.dropDay.map hT
  have hA' : Join.dropDay.map hR ≫ Join.dropDay.map A'.hom =
      Join.dropDay.map A.hom ≫ Join.dropDay.map hO := by
    simpa only [Functor.map_comp] using congrArg Join.dropDay.map hA
  change opFunctor.map (Join.dropDay.map (fD ⊗ₘ gD)) ≫
      ((Join.dropDayReverseIso (F' ⊗ G')).hom ≫
        Join.dropDay.map E'.hom ≫ Join.dropDay.map A'.hom) =
    ((Join.dropDayReverseIso (F ⊗ G)).hom ≫
      Join.dropDay.map E.hom ≫ Join.dropDay.map A.hom) ≫ Join.dropDay.map hO
  calc
    opFunctor.map (Join.dropDay.map (fD ⊗ₘ gD)) ≫
        ((Join.dropDayReverseIso (F' ⊗ G')).hom ≫
          Join.dropDay.map E'.hom ≫ Join.dropDay.map A'.hom) =
      (opFunctor.map (Join.dropDay.map (fD ⊗ₘ gD)) ≫
        (Join.dropDayReverseIso (F' ⊗ G')).hom) ≫
          (Join.dropDay.map E'.hom ≫ Join.dropDay.map A'.hom) := by
            simp only [Category.assoc]
    _ = ((Join.dropDayReverseIso (F ⊗ G)).hom ≫ Join.dropDay.map fR) ≫
        (Join.dropDay.map E'.hom ≫ Join.dropDay.map A'.hom) := by rw [hD]
    _ = (Join.dropDayReverseIso (F ⊗ G)).hom ≫
        ((Join.dropDay.map fR ≫ Join.dropDay.map E'.hom) ≫ Join.dropDay.map A'.hom) := by
          simp only [Category.assoc]
    _ = (Join.dropDayReverseIso (F ⊗ G)).hom ≫
        ((Join.dropDay.map E.hom ≫ Join.dropDay.map hR) ≫ Join.dropDay.map A'.hom) := by
          rw [hT']
    _ = (Join.dropDayReverseIso (F ⊗ G)).hom ≫
        (Join.dropDay.map E.hom ≫ (Join.dropDay.map hR ≫ Join.dropDay.map A'.hom)) := by
          simp only [Category.assoc]
    _ = (Join.dropDayReverseIso (F ⊗ G)).hom ≫
        (Join.dropDay.map E.hom ≫ (Join.dropDay.map A.hom ≫ Join.dropDay.map hO)) := by
          rw [hA']
    _ = ((Join.dropDayReverseIso (F ⊗ G)).hom ≫
        Join.dropDay.map E.hom ≫ Join.dropDay.map A.hom) ≫ Join.dropDay.map hO := by
          simp only [Category.assoc]

/-- The first original join factor becomes the second original opposite factor. -/
@[reassoc]
theorem _root_.SSet.op_joinInl_comp_joinOppositeIso_hom (X Y : SSet.{u}) :
    opFunctor.map (joinInl X Y) ≫ (joinOppositeIso X Y).hom = joinInr Y.op X.op := by
  apply NatTrans.ext
  funext n
  obtain ⟨a, rfl⟩ : ∃ a, n = op a := ⟨n.unop, rfl⟩
  apply ConcreteCategory.hom_ext
  intro x
  let F := Join.augDay.obj X
  let G := Join.augDay.obj Y
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  change (joinOppositeIso X Y).hom.app (op a)
      (opObjEquiv.symm ((joinInl X Y).app (op a) (opObjEquiv x))) =
    (joinInr Y.op X.op).app (op a) x
  rw [SSet.joinInl_app_eq_η, SSet.joinInr_app_eq_η]
  change (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p
      ((Join.reverseTensorDayIso F G).hom.natTrans.app p
        ((DayFunctor.η F G).app (p, op WithInitial.star) (opObjEquiv x, PUnit.unit))) =
    (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
      (op WithInitial.star, p) (PUnit.unit, x)
  have hγ : (Join.reverseTensorDayIso F G).hom.natTrans.app p
      ((DayFunctor.η F G).app (p, op WithInitial.star) (opObjEquiv x, PUnit.unit)) =
      (DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
        (op WithInitial.star, p) (PUnit.unit, opObjEquiv x) := by
    exact Join.reverseTensorDayIso_hom_leftPoint F G a (opObjEquiv x) PUnit.unit
  rw [hγ]
  have hs : (DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
      (op WithInitial.star, p) ≫
        (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p =
      ((Join.augDayReverseIso Y).hom.natTrans.app (op WithInitial.star) ⊗ₘ
        (Join.augDayReverseIso X).hom.natTrans.app p) ≫
          (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
            (op WithInitial.star, p) :=
    Join.η_tensorHom_app (Join.augDayReverseIso Y).hom (Join.augDayReverseIso X).hom
      (op WithInitial.star) p
  have hv : ((Join.augDayReverseIso Y).hom.natTrans.app (op WithInitial.star) ⊗ₘ
      (Join.augDayReverseIso X).hom.natTrans.app p) (PUnit.unit, opObjEquiv x) =
      (PUnit.unit, x) := by
    have hx : (Join.augDayReverseIso X).hom.natTrans.app p (opObjEquiv x) = x :=
      (Join.augDayReverseIso_hom_app_of X a (opObjEquiv x)).trans
        (opObjEquiv.symm_apply_apply x)
    exact (CategoryTheory.tensor_apply _ _ _).trans
      (congrArg₂ Prod.mk (Join.augDayReverseIso_hom_app_star Y) hx)
  have h : (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p
      ((DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
        (op WithInitial.star, p) (PUnit.unit, opObjEquiv x)) =
      (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
        (op WithInitial.star, p)
        (((Join.augDayReverseIso Y).hom.natTrans.app (op WithInitial.star) ⊗ₘ
          (Join.augDayReverseIso X).hom.natTrans.app p) (PUnit.unit, opObjEquiv x)) :=
    types_congr_hom hs (PUnit.unit, opObjEquiv x)
  exact h.trans (congrArg
    ((DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
      (op WithInitial.star, p)) hv)

/-- The second original join factor becomes the first original opposite factor. -/
@[reassoc]
theorem _root_.SSet.op_joinInr_comp_joinOppositeIso_hom (X Y : SSet.{u}) :
    opFunctor.map (joinInr X Y) ≫ (joinOppositeIso X Y).hom = joinInl Y.op X.op := by
  apply NatTrans.ext
  funext n
  obtain ⟨a, rfl⟩ : ∃ a, n = op a := ⟨n.unop, rfl⟩
  apply ConcreteCategory.hom_ext
  intro y
  let F := Join.augDay.obj X
  let G := Join.augDay.obj Y
  let p : AugmentedSimplexCategoryᵒᵖ := op (WithInitial.of a)
  change (joinOppositeIso X Y).hom.app (op a)
      (opObjEquiv.symm ((joinInr X Y).app (op a) (opObjEquiv y))) =
    (joinInl Y.op X.op).app (op a) y
  rw [SSet.joinInr_app_eq_η, SSet.joinInl_app_eq_η]
  change (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p
      ((Join.reverseTensorDayIso F G).hom.natTrans.app p
        ((DayFunctor.η F G).app (op WithInitial.star, p) (PUnit.unit, opObjEquiv y))) =
    (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
      (p, op WithInitial.star) (y, PUnit.unit)
  have hγ : (Join.reverseTensorDayIso F G).hom.natTrans.app p
      ((DayFunctor.η F G).app (op WithInitial.star, p) (PUnit.unit, opObjEquiv y)) =
      (DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
        (p, op WithInitial.star) (opObjEquiv y, PUnit.unit) := by
    exact Join.reverseTensorDayIso_hom_rightPoint F G a PUnit.unit (opObjEquiv y)
  rw [hγ]
  have hs : (DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
      (p, op WithInitial.star) ≫
        (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p =
      ((Join.augDayReverseIso Y).hom.natTrans.app p ⊗ₘ
        (Join.augDayReverseIso X).hom.natTrans.app (op WithInitial.star)) ≫
          (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
            (p, op WithInitial.star) :=
    Join.η_tensorHom_app (Join.augDayReverseIso Y).hom (Join.augDayReverseIso X).hom
      p (op WithInitial.star)
  have hv : ((Join.augDayReverseIso Y).hom.natTrans.app p ⊗ₘ
      (Join.augDayReverseIso X).hom.natTrans.app (op WithInitial.star))
        (opObjEquiv y, PUnit.unit) = (y, PUnit.unit) := by
    have hy : (Join.augDayReverseIso Y).hom.natTrans.app p (opObjEquiv y) = y :=
      (Join.augDayReverseIso_hom_app_of Y a (opObjEquiv y)).trans
        (opObjEquiv.symm_apply_apply y)
    exact (CategoryTheory.tensor_apply _ _ _).trans
      (congrArg₂ Prod.mk hy (Join.augDayReverseIso_hom_app_star X))
  have h : (tensorIso (Join.augDayReverseIso Y) (Join.augDayReverseIso X)).hom.natTrans.app p
      ((DayFunctor.η (Join.reverseDay G) (Join.reverseDay F)).app
        (p, op WithInitial.star) (opObjEquiv y, PUnit.unit)) =
      (DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
        (p, op WithInitial.star)
        (((Join.augDayReverseIso Y).hom.natTrans.app p ⊗ₘ
          (Join.augDayReverseIso X).hom.natTrans.app (op WithInitial.star))
            (opObjEquiv y, PUnit.unit)) :=
    types_congr_hom hs (opObjEquiv y, PUnit.unit)
  exact h.trans (congrArg
    ((DayFunctor.η (Join.augDay.obj Y.op) (Join.augDay.obj X.op)).app
      (p, op WithInitial.star)) hv)

end SSet.Join
