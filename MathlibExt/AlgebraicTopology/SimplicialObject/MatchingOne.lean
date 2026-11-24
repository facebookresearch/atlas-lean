/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Matching
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Degree-one matching objects and their labelled faces

The actual matching limit in degree one is naturally the chosen product of two copies of degree
zero. The first projection is the face indexed by `δ₀`, the second by `δ₁`. The comparison of whole
matching arrows keeps the identity on degree one. A separate explicit product swap gives the
source–target order `(d₁,d₀)`.

Only binary products and limits of the actual degree-one matching-index shape are required. The
coefficient category has independent object and morphism universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- The original degree-one matching face. Index zero selects vertex one; index one selects
vertex zero. -/
abbrev matchingOneFace (i : Fin 2) : matchingIndex 1 where
  obj := StructuredArrow.mk (SimplexCategory.δ i).op
  property := ⟨by dsimp; infer_instance, by change 0 < 1; decide⟩

private theorem rightZero (a : matchingIndex 1) : a.obj.right = op ⦋0⦌ := by
  apply unop_injective
  exact SimplexCategory.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ a.property.2))

private def label (a : matchingIndex 1) : Fin 2 :=
  a.obj.hom.unop.toOrderHom 0

private theorem label_face_zero : label (matchingOneFace 0) = 1 := by decide

private theorem label_face_one : label (matchingOneFace 1) = 0 := by decide

private theorem exhaustive (a : matchingIndex 1) :
    a = matchingOneFace 0 ∨ a = matchingOneFace 1 := by
  let θ : ⦋0⦌ ⟶ ⦋1⦌ := (eqToHom (rightZero a)).unop ≫ a.obj.hom.unop
  let _ : Mono a.obj.hom.unop := a.property.1
  let _ : Mono θ := by dsimp [θ]; infer_instance
  obtain ⟨i, hi⟩ := SimplexCategory.eq_δ_of_mono θ
  have ha : a = matchingOneFace i := by
    apply ObjectProperty.FullSubcategory.ext
    apply StructuredArrow.obj_ext a.obj (matchingOneFace i).obj (rightZero a)
    apply Quiver.Hom.unop_inj
    change θ = SimplexCategory.δ i
    exact hi
  cases i using Fin.cases with
  | zero => exact Or.inl ha
  | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Or.inr ha

private theorem rightHomSubsingleton (a b : matchingIndex 1) :
    Subsingleton (a.obj.right ⟶ b.obj.right) := by
  rw [rightZero a, rightZero b]
  infer_instance

private theorem eq_of_hom {a b : matchingIndex 1} (f : a ⟶ b) : a = b := by
  let _ := rightHomSubsingleton a b
  have hr : a.obj.right = b.obj.right := (rightZero a).trans (rightZero b).symm
  have hf : f.hom.right = eqToHom hr := Subsingleton.elim _ _
  apply ObjectProperty.FullSubcategory.ext
  apply StructuredArrow.obj_ext a.obj b.obj hr
  rw [← hf]
  exact StructuredArrow.w f.hom

variable {C : Type u} [Category.{v} C]

private def oneCone (X : SimplicialObject C) {T : C}
    (f g : T ⟶ X.obj (op ⦋0⦌)) : Cone (matchingDiagram X 1) where
  pt := T
  π :=
    { app := fun a => (if label a = 1 then f else g) ≫
        X.map (eqToHom (rightZero a).symm)
      naturality := by
        intro a b h
        obtain rfl := eq_of_hom h
        let _ := rightHomSubsingleton a a
        have hh : h.hom.right = 𝟙 a.obj.right := Subsingleton.elim _ _
        change 𝟙 T ≫ _ = _ ≫ X.map h.hom.right
        rw [hh, X.map_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm }

private theorem oneCone_zero (X : SimplicialObject C) {T : C}
    (f g : T ⟶ X.obj (op ⦋0⦌)) : (oneCone X f g).π.app (matchingOneFace 0) = f := by
  change (if label (matchingOneFace 0) = 1 then f else g) ≫
    X.map (eqToHom (rightZero (matchingOneFace 0)).symm) = f
  rw [label_face_zero]
  simp

private theorem oneCone_one (X : SimplicialObject C) {T : C}
    (f g : T ⟶ X.obj (op ⦋0⦌)) : (oneCone X f g).π.app (matchingOneFace 1) = g := by
  change (if label (matchingOneFace 1) = 1 then f else g) ≫
    X.map (eqToHom (rightZero (matchingOneFace 1)).symm) = g
  rw [label_face_one]
  simp

variable [HasLimitsOfShape (matchingIndex 1) C] [HasBinaryProducts C]

private abbrev oneFan (X : SimplicialObject C) :
    BinaryFan (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌)) :=
  BinaryFan.mk (matchingπ X 1 (matchingOneFace 0)) (matchingπ X 1 (matchingOneFace 1))

private def oneFanIsLimit (X : SimplicialObject C) : IsLimit (oneFan X) :=
  BinaryFan.IsLimit.mk _
    (fun f g => limit.lift (matchingDiagram X 1) (oneCone X f g))
    (by
      intro T f g
      exact (limit.lift_π (oneCone X f g) (matchingOneFace 0)).trans (oneCone_zero X f g))
    (by
      intro T f g
      exact (limit.lift_π (oneCone X f g) (matchingOneFace 1)).trans (oneCone_one X f g))
    (by
      intro T f g m hf hg
      apply limit.hom_ext (F := matchingDiagram X 1)
      intro a
      rcases exhaustive a with rfl | rfl
      · exact hf.trans ((limit.lift_π (oneCone X f g) (matchingOneFace 0)).trans
          (oneCone_zero X f g)).symm
      · exact hg.trans ((limit.lift_π (oneCone X f g) (matchingOneFace 1)).trans
          (oneCone_one X f g)).symm)

private def componentIso (X : SimplicialObject C) :
    matchingObject X 1 ≅ X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) :=
  (oneFanIsLimit X).conePointUniqueUpToIso
    (limit.isLimit (pair (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))))

private theorem componentIso_fst (X : SimplicialObject C) :
    (componentIso X).hom ≫ prod.fst = matchingπ X 1 (matchingOneFace 0) :=
  (oneFanIsLimit X).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌)))) ⟨WalkingPair.left⟩

private theorem componentIso_snd (X : SimplicialObject C) :
    (componentIso X).hom ≫ prod.snd = matchingπ X 1 (matchingOneFace 1) :=
  (oneFanIsLimit X).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌)))) ⟨WalkingPair.right⟩

private abbrev zeroProductFunctor : SimplicialObject C ⥤ C :=
  (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌) ⋙
    Functor.diag C ⋙ Functor.uncurry.obj (prod.functor : C ⥤ C ⥤ C)

omit [HasLimitsOfShape (matchingIndex 1) C] in
private theorem zeroProductFunctor_map {X Y : SimplicialObject C} (f : X ⟶ Y) :
    zeroProductFunctor.map f = prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) := by
  simp [zeroProductFunctor, Functor.diag, Functor.uncurry, prod.functor, prod.map_map]

private theorem componentIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingObjectFunctor 1).map f ≫ (componentIso Y).hom =
      (componentIso X).hom ≫ prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) := by
  apply prod.hom_ext
  · rw [Category.assoc, componentIso_fst, matchingObjectFunctor_map_π,
      Category.assoc, prod.map_fst, ← Category.assoc, componentIso_fst]
    rfl
  · rw [Category.assoc, componentIso_snd, matchingObjectFunctor_map_π,
      Category.assoc, prod.map_snd, ← Category.assoc, componentIso_snd]
    rfl

/-- The chosen degree-one matching limit is naturally the chosen degree-zero product. The
projection order is `(d₀,d₁)`. -/
@[no_expose]
def matchingOneIso :
    matchingObjectFunctor (C := C) 1 ≅
      (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌) ⋙
        Functor.diag C ⋙ Functor.uncurry.obj (prod.functor : C ⥤ C ⥤ C) :=
  NatIso.ofComponents componentIso (by
    intro X Y f
    change (matchingObjectFunctor 1).map f ≫ (componentIso Y).hom =
      (componentIso X).hom ≫ zeroProductFunctor.map f
    rw [zeroProductFunctor_map]
    exact componentIso_naturality f)

/-- The first product projection retains the original matching face `δ₀`. -/
@[reassoc (attr := simp)]
theorem matchingOneIso_hom_fst (X : SimplicialObject C) :
    matchingOneIso.hom.app X ≫
        (prod.fst : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) =
      matchingπ X 1 (matchingOneFace 0) :=
  componentIso_fst X

/-- The second product projection retains the original matching face `δ₁`. -/
@[reassoc (attr := simp)]
theorem matchingOneIso_hom_snd (X : SimplicialObject C) :
    matchingOneIso.hom.app X ≫
        (prod.snd : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) =
      matchingπ X 1 (matchingOneFace 1) :=
  componentIso_snd X

/-- The inverse comparison retains the first labelled matching projection. -/
@[reassoc (attr := simp)]
theorem matchingOneIso_inv_fst (X : SimplicialObject C) :
    matchingOneIso.inv.app X ≫ matchingπ X 1 (matchingOneFace 0) =
      (prod.fst : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) := by
  rw [← matchingOneIso_hom_fst X, Iso.inv_hom_id_app_assoc]

/-- The inverse comparison retains the second labelled matching projection. -/
@[reassoc (attr := simp)]
theorem matchingOneIso_inv_snd (X : SimplicialObject C) :
    matchingOneIso.inv.app X ≫ matchingπ X 1 (matchingOneFace 1) =
      (prod.snd : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) := by
  rw [← matchingOneIso_hom_snd X, Iso.inv_hom_id_app_assoc]

/-- The original matching map becomes the original ordered face pair `(d₀,d₁)`. -/
@[reassoc]
theorem matchingOneIso_matchingMap (X : SimplicialObject C) :
    matchingMap X 1 ≫ matchingOneIso.hom.app X = prod.lift (X.δ 0) (X.δ 1) := by
  apply prod.hom_ext (X := X.obj (op ⦋0⦌)) (Y := X.obj (op ⦋0⦌))
  · rw [Category.assoc, matchingOneIso_hom_fst, matchingMap_π]
    change X.δ 0 = prod.lift (X.δ 0) (X.δ 1) ≫ prod.fst
    exact (prod.lift_fst (X.δ 0) (X.δ 1)).symm
  · rw [Category.assoc, matchingOneIso_hom_snd, matchingMap_π]
    change X.δ 1 = prod.lift (X.δ 0) (X.δ 1) ≫ prod.snd
    exact (prod.lift_snd (X.δ 0) (X.δ 1)).symm

/-- Forward naturality for every original simplicial morphism. -/
@[reassoc]
theorem matchingOneIso_hom_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingObjectFunctor 1).map f ≫ matchingOneIso.hom.app Y =
      matchingOneIso.hom.app X ≫ prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) := by
  simpa only [zeroProductFunctor_map] using matchingOneIso.hom.naturality f

/-- Inverse naturality for every original simplicial morphism. -/
@[reassoc]
theorem matchingOneIso_inv_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) ≫ matchingOneIso.inv.app Y =
      matchingOneIso.inv.app X ≫ (matchingObjectFunctor 1).map f := by
  simpa only [zeroProductFunctor_map] using matchingOneIso.inv.naturality f

private def zeroSwapIso : zeroProductFunctor (C := C) ≅ zeroProductFunctor :=
  NatIso.ofComponents (fun X => prod.braiding (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))) (by
    intro X Y f
    simpa only [zeroProductFunctor_map] using
      braid_natural (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)))

/-- The explicit product swap gives the source–target matching order `(d₁,d₀)`. -/
@[no_expose]
def matchingOneSourceTargetIso :
    matchingObjectFunctor (C := C) 1 ≅
      (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋0⦌) ⋙
        Functor.diag C ⋙ Functor.uncurry.obj (prod.functor : C ⥤ C ⥤ C) :=
  matchingOneIso ≪≫ zeroSwapIso

/-- The forward source–target comparison is exactly the native product swap after the original
matching comparison. -/
theorem matchingOneSourceTargetIso_hom_eq (X : SimplicialObject C) :
    matchingOneSourceTargetIso.hom.app X = matchingOneIso.hom.app X ≫
      (prod.braiding (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))).hom := by rfl

/-- Its inverse is exactly the native inverse product swap before the original inverse. -/
theorem matchingOneSourceTargetIso_inv_eq (X : SimplicialObject C) :
    matchingOneSourceTargetIso.inv.app X =
      (prod.braiding (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))).inv ≫
        matchingOneIso.inv.app X := by rfl

/-- In source–target order, the first projection is the original `δ₁` matching leg. -/
@[reassoc (attr := simp)]
theorem matchingOneSourceTargetIso_hom_fst (X : SimplicialObject C) :
    matchingOneSourceTargetIso.hom.app X ≫
        (prod.fst : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) =
      matchingπ X 1 (matchingOneFace 1) := by
  change (matchingOneIso.hom.app X ≫
    (prod.braiding (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))).hom) ≫ prod.fst = _
  rw [Category.assoc]
  simp only [prod.braiding, prod.lift_fst]
  exact matchingOneIso_hom_snd X

/-- In source–target order, the second projection is the original `δ₀` matching leg. -/
@[reassoc (attr := simp)]
theorem matchingOneSourceTargetIso_hom_snd (X : SimplicialObject C) :
    matchingOneSourceTargetIso.hom.app X ≫
        (prod.snd : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) =
      matchingπ X 1 (matchingOneFace 0) := by
  change (matchingOneIso.hom.app X ≫
    (prod.braiding (X.obj (op ⦋0⦌)) (X.obj (op ⦋0⦌))).hom) ≫ prod.snd = _
  rw [Category.assoc]
  simp only [prod.braiding, prod.lift_snd]
  exact matchingOneIso_hom_fst X

/-- The inverse source–target comparison retains its first labelled leg. -/
@[reassoc (attr := simp)]
theorem matchingOneSourceTargetIso_inv_fst (X : SimplicialObject C) :
    matchingOneSourceTargetIso.inv.app X ≫ matchingπ X 1 (matchingOneFace 1) =
      (prod.fst : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) := by
  rw [← matchingOneSourceTargetIso_hom_fst X, Iso.inv_hom_id_app_assoc]

/-- The inverse source–target comparison retains its second labelled leg. -/
@[reassoc (attr := simp)]
theorem matchingOneSourceTargetIso_inv_snd (X : SimplicialObject C) :
    matchingOneSourceTargetIso.inv.app X ≫ matchingπ X 1 (matchingOneFace 0) =
      (prod.snd : X.obj (op ⦋0⦌) ⨯ X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋0⦌)) := by
  rw [← matchingOneSourceTargetIso_hom_snd X, Iso.inv_hom_id_app_assoc]

/-- The same original matching map becomes the explicitly swapped pair `(d₁,d₀)`. -/
@[reassoc]
theorem matchingOneSourceTargetIso_matchingMap (X : SimplicialObject C) :
    matchingMap X 1 ≫ matchingOneSourceTargetIso.hom.app X =
      prod.lift (X.δ 1) (X.δ 0) := by
  apply prod.hom_ext (X := X.obj (op ⦋0⦌)) (Y := X.obj (op ⦋0⦌))
  · rw [Category.assoc, matchingOneSourceTargetIso_hom_fst, matchingMap_π]
    change X.δ 1 = prod.lift (X.δ 1) (X.δ 0) ≫ prod.fst
    exact (prod.lift_fst (X.δ 1) (X.δ 0)).symm
  · rw [Category.assoc, matchingOneSourceTargetIso_hom_snd, matchingMap_π]
    change X.δ 0 = prod.lift (X.δ 1) (X.δ 0) ≫ prod.snd
    exact (prod.lift_snd (X.δ 1) (X.δ 0)).symm

/-- Forward naturality of the explicitly swapped comparison. -/
@[reassoc]
theorem matchingOneSourceTargetIso_hom_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingObjectFunctor 1).map f ≫ matchingOneSourceTargetIso.hom.app Y =
      matchingOneSourceTargetIso.hom.app X ≫
        prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) := by
  simpa only [zeroProductFunctor_map] using
    matchingOneSourceTargetIso.hom.naturality f

/-- Inverse naturality of the explicitly swapped comparison. -/
@[reassoc]
theorem matchingOneSourceTargetIso_inv_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) ≫
        matchingOneSourceTargetIso.inv.app Y =
      matchingOneSourceTargetIso.inv.app X ≫ (matchingObjectFunctor 1).map f := by
  simpa only [zeroProductFunctor_map] using
    matchingOneSourceTargetIso.inv.naturality f

omit [HasLimitsOfShape (matchingIndex 1) C] in
private theorem facePairSquare (i j : Fin 2) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋1⦌) ≫ prod.lift (Y.δ i) (Y.δ j) =
      prod.lift (X.δ i) (X.δ j) ≫
        prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌)) := by
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
      using (δ_naturality f i).symm
  · simpa only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      using (δ_naturality f j).symm

/-- The whole original face-pair arrows in order `(d₀,d₁)`. -/
def matchingOnePairArrowFunctor : SimplicialObject C ⥤ Arrow C where
  obj X := Arrow.mk (prod.lift (X.δ 0) (X.δ 1))
  map f := Arrow.homMk (f.app (op ⦋1⦌))
    (prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌))) (by exact facePairSquare 0 1 f)
  map_id X := by
    apply Arrow.hom_ext
    · rfl
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · simp only [Arrow.homMk_right, Arrow.comp_right, NatTrans.comp_app, prod.map_map]

/-- The whole original face-pair arrows in source–target order `(d₁,d₀)`. -/
def matchingOneSourceTargetArrowFunctor : SimplicialObject C ⥤ Arrow C where
  obj X := Arrow.mk (prod.lift (X.δ 1) (X.δ 0))
  map f := Arrow.homMk (f.app (op ⦋1⦌))
    (prod.map (f.app (op ⦋0⦌)) (f.app (op ⦋0⦌))) (by exact facePairSquare 1 0 f)
  map_id X := by
    apply Arrow.hom_ext
    · rfl
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · simp only [Arrow.homMk_right, Arrow.comp_right, NatTrans.comp_app, prod.map_map]

/-- The natural comparison of whole matching arrows retains identity on the original X₁. -/
def matchingOneArrowIso :
    matchingMapArrowFunctor (C := C) 1 ≅ matchingOnePairArrowFunctor :=
  NatIso.ofComponents
    (fun X => Arrow.isoMk (Iso.refl _) (matchingOneIso.app X)
      (by
        change 𝟙 (X.obj (op ⦋1⦌)) ≫ prod.lift (X.δ 0) (X.δ 1) =
          matchingMap X 1 ≫ matchingOneIso.hom.app X
        rw [Category.id_comp]
        exact (matchingOneIso_matchingMap X).symm))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change f.app (op ⦋1⦌) ≫ 𝟙 _ = 𝟙 _ ≫ f.app (op ⦋1⦌)
        simp
      · exact matchingOneIso_hom_naturality f)

/-- Forward comparison of whole arrows keeps the original source. -/
@[simp]
theorem matchingOneArrowIso_hom_left (X : SimplicialObject C) :
    (matchingOneArrowIso.hom.app X).left = 𝟙 (X.obj (op ⦋1⦌)) := rfl

/-- Inverse comparison of whole arrows keeps the original source. -/
@[simp]
theorem matchingOneArrowIso_inv_left (X : SimplicialObject C) :
    (matchingOneArrowIso.inv.app X).left = 𝟙 (X.obj (op ⦋1⦌)) := rfl

/-- The target of the forward whole-arrow comparison is the chosen matching/product comparison. -/
@[simp]
theorem matchingOneArrowIso_hom_right (X : SimplicialObject C) :
    (matchingOneArrowIso.hom.app X).right = matchingOneIso.hom.app X := rfl

/-- The target of the inverse whole-arrow comparison is its actual inverse. -/
@[simp]
theorem matchingOneArrowIso_inv_right (X : SimplicialObject C) :
    (matchingOneArrowIso.inv.app X).right = matchingOneIso.inv.app X := rfl

/-- Forward naturality of the whole original Arrow comparison. -/
theorem matchingOneArrowIso_hom_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingMapArrowFunctor 1).map f ≫ matchingOneArrowIso.hom.app Y =
      matchingOneArrowIso.hom.app X ≫ matchingOnePairArrowFunctor.map f :=
  matchingOneArrowIso.hom.naturality f

/-- Inverse naturality of the whole original Arrow comparison. -/
theorem matchingOneArrowIso_inv_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    matchingOnePairArrowFunctor.map f ≫ matchingOneArrowIso.inv.app Y =
      matchingOneArrowIso.inv.app X ≫ (matchingMapArrowFunctor 1).map f :=
  matchingOneArrowIso.inv.naturality f

/-- The explicit product swap also compares whole matching arrows, with the same identity
source on X₁. -/
def matchingOneSourceTargetArrowIso :
    matchingMapArrowFunctor (C := C) 1 ≅ matchingOneSourceTargetArrowFunctor :=
  NatIso.ofComponents
    (fun X => Arrow.isoMk (Iso.refl _) (matchingOneSourceTargetIso.app X)
      (by
        change 𝟙 (X.obj (op ⦋1⦌)) ≫ prod.lift (X.δ 1) (X.δ 0) =
          matchingMap X 1 ≫ matchingOneSourceTargetIso.hom.app X
        rw [Category.id_comp]
        exact (matchingOneSourceTargetIso_matchingMap X).symm))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change f.app (op ⦋1⦌) ≫ 𝟙 _ = 𝟙 _ ≫ f.app (op ⦋1⦌)
        simp
      · exact matchingOneSourceTargetIso_hom_naturality f)

/-- Swapping the target product retains the original source in the forward direction. -/
@[simp]
theorem matchingOneSourceTargetArrowIso_hom_left (X : SimplicialObject C) :
    (matchingOneSourceTargetArrowIso.hom.app X).left = 𝟙 (X.obj (op ⦋1⦌)) := rfl

/-- Swapping the target product retains the original source in the inverse direction. -/
@[simp]
theorem matchingOneSourceTargetArrowIso_inv_left (X : SimplicialObject C) :
    (matchingOneSourceTargetArrowIso.inv.app X).left = 𝟙 (X.obj (op ⦋1⦌)) := rfl

/-- The forward target is the explicit source–target matching comparison. -/
@[simp]
theorem matchingOneSourceTargetArrowIso_hom_right (X : SimplicialObject C) :
    (matchingOneSourceTargetArrowIso.hom.app X).right =
      matchingOneSourceTargetIso.hom.app X := rfl

/-- The inverse target is the actual inverse of the explicit source–target comparison. -/
@[simp]
theorem matchingOneSourceTargetArrowIso_inv_right (X : SimplicialObject C) :
    (matchingOneSourceTargetArrowIso.inv.app X).right =
      matchingOneSourceTargetIso.inv.app X := rfl

/-- Forward naturality of the explicitly swapped whole Arrow comparison. -/
theorem matchingOneSourceTargetArrowIso_hom_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingMapArrowFunctor 1).map f ≫ matchingOneSourceTargetArrowIso.hom.app Y =
      matchingOneSourceTargetArrowIso.hom.app X ≫ matchingOneSourceTargetArrowFunctor.map f :=
  matchingOneSourceTargetArrowIso.hom.naturality f

/-- Inverse naturality of the explicitly swapped whole Arrow comparison. -/
theorem matchingOneSourceTargetArrowIso_inv_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    matchingOneSourceTargetArrowFunctor.map f ≫ matchingOneSourceTargetArrowIso.inv.app Y =
      matchingOneSourceTargetArrowIso.inv.app X ≫ (matchingMapArrowFunctor 1).map f :=
  matchingOneSourceTargetArrowIso.inv.naturality f

end CategoryTheory.SimplicialObject
